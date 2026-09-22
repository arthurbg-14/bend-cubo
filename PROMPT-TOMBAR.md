# Tarefa: as 10 leis que faltam depois do conserto do tombo (21/09/2026)

## Estado

O JOGO está corrigido e testado (`./fast`: quina e saliência 0,55/0,60/0,70
OK; saliência 0,50 removida do teste, é o ponto de equilíbrio sem torque,
não decidível por física). As 25 leis antigas (`LAWS.bend`) seguem provadas
com a física nova — ver o commit desta sessão. Faltam 10:
`past_the_edge_it_tips_{px,nx,pz,nz}`, `tipping_is_never_thrown_away_{px,nx,
pz,nz}`, `on_a_corner_it_tips_{x,z}`.

## O que mudou na física (por que as leis agora são verdadeiras)

1. **`Body.spin`** (`phys.bend`): decide manter ou zerar o giro **uma vez**,
   depois da busca inteira (`Tick.moved(final, rt)` compara só o quatérnio
   final contra o original) — nunca dentro do `Tick.put`/`Tick.pivot` (isso
   custava ~50x no checador, medido). Mantém quando `tip` (braço fora do
   meio, `|rx|+|rz|>0`) é verdadeiro.
2. **`Tick.shrink`/`Tick.cand`**: a busca por giro que caiba (cheio, metade,
   um quarto, ..., até 1/128 — 7 tentativas). Um candidato só não bastava
   (passava por cima do encaixe).
3. **`Geo.foot`/`Geo.widex`/`Geo.widez`**: o pé de apoio agora usa a sombra do
   cubo virado (mais largo que a caixa reta), não só a caixa.
4. **`Hold.face`**: parado numa face (sem vizinho), se as três direções caem
   na zona morta, o braço de apoio é zero (senão pressiona fora do centro
   numa face quase reta e nunca fica plano).
5. **Zona morta (`Z.dead`)**: de meio grau (512) para um vigésimo de grau
   (64) — a antiga deixava o cubo apoiado fora do centro assim que começava
   a girar.

## A matemática das 10 leis (derivada, não escrita em Bend ainda)

Para um corpo parado (v=0, giro 0), apoiado, no chão ou num vizinho:

- `Body.step` (a parte linear do tique) **não muda o quatérnio**, só o giro:
  `w_passo = Rot.kickd(Rot.about(s,ax,ay,az), ax,ay,az, Pos{0},Pos{g},Pos{0})`
  onde `(ax,ay,az) = Hold.low(Rot.mat(q),s)` (chão) ou
  `Hold.arm(Geo.foot(...), Rot.mat(q), s)` (vizinho) — o braço da própria lei.
- `w_passo.z = Z.divc(Rot.crz(ax,ay,0,g), d)`, mesmo sinal de `ax*g`; como
  `g>0` (hipótese `heavy`), mesmo sinal de `ax`. Logo `ax * w_passo.z > 0`
  sempre que `ax≠0` (hipótese `off`/`across`) — é exatamente a conclusão de
  `on_a_corner_it_tips_x` e o "braço" de `past_the_edge`/`tipping`.
- `Tick.spin` depois: como `w_passo≠0`, entra em `Tick.turn2(held,floor,...)`
  → `Tick.pivota(...,a=Hold.low/arm(...))` — **o mesmo braço** (`q` não mudou
  no passo). Duas saídas:
  - o giro moveu o quatérnio → 1º disjuntor da lei, pronto;
  - não moveu → por `Body.spin`, giro final = `Pick.w(tip,Rot.w(rt),zero)` =
    `w_passo` (mantido, `tip` é verdade pois `ax≠0`) → cai no cálculo acima.

A lei fecha matematicamente. `past_the_edge_*` usa a mesma cadeia trocando
`Hold.low` por `Hold.arm(Geo.foot(...))` — precisa também que a hipótese
`past` (o meio passou da borda do vizinho) fixe o sinal do braço via
`Geo.leanf` (o grampo na borda do apoio — ainda não derivado, é o próximo
passo dessa família). `tipping_is_never_thrown_away_*` compõe
`past_the_edge` com o MESMO argumento moved-ou-mantido (dado
`past_the_edge`, é quase de graça).

## Armadilhas encontradas tentando escrever isso em Bend

- **`Pos{0n}` e `Neg{0n}` não são o mesmo termo** (mesmo "sendo o mesmo
  zero" fisicamente). Uma lema genérica como `Z.add(v, Pos{0n}) == v` para
  QUALQUER `v` é **falsa como escrita** (falha em `v = Neg{0n}`, dá
  `Pos{0n}` do lado esquerdo). Só prove instâncias onde o valor que recebe o
  zero somado tem magnitude **conhecidamente não-zero** (como
  `Z.mul(ax,g)` aqui, com `ax≠0` e `g>0`) — nesses casos as lemas pequenas
  (`add_zero`/`sub_zero_r` em `ring.bend`/kit, mais `lt_zero_r`:
  `Nat.is_lt(x,0n)==False{}`, trivial por match em `x`) bastam.
- `Nat.add`/`Nat.sub` no Base recursam no **primeiro** argumento: `Nat.add(a,
  0n)==a` precisa indução (não é `{==}`); `Nat.add(0n,a)==a` é **direto**
  (`match a: case 0n: b`, primeiro caso). Escolher a ORDEM dos operandos que
  já reduz de graça antes de escrever a lema.
- Rescrita nas provas: `%e : T` com `e : {A==B}` e `T` = o tipo-alvo com `_`
  no lugar de `B` (não `A`) — ver `Equal.cong`'s próprio corpo em `bend base
  Equal.cong` como referência canônica.
- Constantes/construtores (`P.Pos`, `P.Neg`) não passam direto como `f` de
  `Equal.cong` (erro "a defined name"/mismatch de quantidade `-`/`+`); use o
  `%e : T` inline em vez de chamar `Equal.cong` com o construtor.

## Ordem de trabalho sugerida

1. `on_a_corner_it_tips_x` — sem vizinho, usa `Hold.low` direto. O mais
   simples; a cadeia acima já está pronta, falta só escrever em Bend as
   ~15-30 lemas pequenas (Z.divc preserva sinal, Rot.crz/crx dão o produto
   certo, compor Move.stay→Rot.held→Rot.press→Rot.kickd).
2. `on_a_corner_it_tips_z` — espelha `_x` trocando x↔z e ajustando os sinais
   do "right-hand rule" (ver o comentário da lei em `LAWS.bend`).
3. `past_the_edge_it_tips_*4` — mesma cadeia com `Hold.arm(Geo.foot(...))`;
   precisa fixar o sinal do braço via `Geo.leanf` usando a hipótese `past`.
4. `tipping_is_never_thrown_away_*4` — compõe `past_the_edge` com o
   argumento moved-ou-mantido (`Body.spin`), quase imediato dado 3.

Testar cada uma com `./fast` (que já cobre o comportamento numérico) e
`bend PROOF.bend` (ele mesmo, sem CAP externo — mas medir com
`~/.claude2/jobs/4f2a7e15/tmp/cuts/timed.py` se ainda existir, ou refazer o
vigia: `nice -n 19 ionice -c3`, teto de RSS, um checador por vez — a
recursão de 7 níveis do `Tick.shrink` já custa ~40-100 s por família só
para reprovar as 6 famílias antigas, então o total de `bend PROOF.bend`
passa de minutos; não é bug, é o preço da busca por giro).

## Progresso confirmado em 21/09/2026 (sessão de retomada)

Workflow rápido usado: nunca reprovar o `PROOF.bend` inteiro por iteração —
um arquivo escrito (`~/.claude2/jobs/4f2a7e15/tmp/corner/div.bend`, com uma
cópia local de `phys.bend` do lado) testado isoladamente via
`CAP_MB=2500 python3 ~/.claude2/jobs/4f2a7e15/tmp/cuts/timed.py 20|25
.../div.bend` (< 1s por rodada). Só integrar no PROOF.bend real depois de
tudo provado isoladamente.

**A parte matemática dura de `on_a_corner_it_tips_x` está 100% provada**
em `div.bend` (função `kickzsign`, mais toda a cadeia abaixo dela:
`crz_pos`/`crz_neg`, `Z_divc_pos`/`Z_divc_neg`, `mul_pos`, `divceil_pos`,
`kickzsign_pos`/`kickzsign_neg`, `Z_add_zero_l_pos`/`Z_add_zero_l_neg`):

```
def kickzsign(+ax: P.Z, +off: {Nat.is_lt(0n, P.Z.mag(ax)) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +Y: Nat)
  -> {P.Z.above(P.Z.mul(ax, P.Z.divc(P.Rot.crz(ax, ay, P.Pos{0n}, P.Pos{g}), Nat.add(8n, Y))), P.Pos{0n}) == True{} : Bool}
```
Isto é exatamente `ax * w.z > 0` sempre que `ax≠0`, `g>0`, para qualquer
`ay` — o coração da lei. `Y` fica opaco (é o termo de divisão interno de
`Rot.about`; `Rot.about(s,ax,ay,az) = Nat.add(8n,Y)` sempre, pela forma
literal `8n` na definição — nunca escrever a fórmula de `Y` por dentro).

**Confirmado por leitura de código (não precisa provar, só encaixar) que
todo o resto da lei é montagem mecânica, SEM matemática nova**:
- `Tick.pivota0` não usa seu parâmetro `md` (Mat) — a complicação de
  `Rot.mat`/`Tick.fits`/`Tick.place`/`Geo.foot` fica **inteiramente fora**
  da prova: só importa o Bool `Tick.moved(bf,rt)`.
- Ramo `moved=True`: `Tick.moved` é *definido* como
  `Bool.not(Quat.same(Rot.q(Body.rot(b)),Rot.q(rt)))` — então `moved=True`
  já É o primeiro disjuntor da lei, de graça, por definição.
- Ramo `moved=False`: `Body.spin(tip=True,False,bf,rt)` devolve
  `Body.setrot(bf, Rot{Rot.q(bf), Pick.w(True,Rot.w(rt),zero)})` =
  `Rot.w(rt)` mantido — e `Rot.w(rt)` é exatamente `w'` computado no
  `Body.step` (nunca mudou). `w' = Rot.held(True,Rot{q,zero},s,x,y,z,g,[])`
  desenrola (`Rot.pressw`→`Rot.press`→`Rot.kickd`) até
  `Wv.z(w') = Z.add(Pos{0n}, Z.divc(Rot.crz(ax,ay,Pos{0},Pos{g}),
  Rot.about(s,ax,ay,az)))` — e isso é `kickzsign` após absorver o
  `Z.add(Pos{0n}, ·)` com `Z_add_zero_l_pos/neg` (o valor nunca é
  `Neg{0n}` aqui porque `kickzsign` já prova magnitude > 0 — não cai na
  armadilha Pos{0}/Neg{0}).
- `tip=True` vem de `off` (`mag(ax)>0` ⟹ `mag(ax)+mag(az)>0`, fato Nat
  trivial).

**Falta só provar em Bend** (puro encaixe de definições, nenhuma
matemática nova, mas ainda não escrito — era o que um agente Explore
estava mapeando quando a sessão foi cortada):
1. `Body.step1(k,[],In.idle(),b)` com `b` em repouso (v=0) é um no-op na
   posição/velocidade e só seta `rt = Rot{q, w'}` — depende de
   `Move.x`/`Move.z` serem no-op com v0=Pos{0n} e obs=[], e
   `Body.drive(k,In.idle(),b)` não tocar vx/vz.
2. `Geo.held(Quat.flat(q),s,x,y,z,q,[])==True{}` a partir de `floor`+`held`
   (hipóteses da lei) — precisa olhar a definição de `Geo.held`.
3. `Wv.null(w')==False{}` (de `Wv.z(w')≠0`, que já sai de `kickzsign`).
4. Montar tudo em `Laws.on_a_corner_it_tips_x` (ou nome que o `PROOF.bend`
   usa) e só então colar em `PROOF.bend` de verdade.

Depois disso, `on_a_corner_it_tips_z` é a MESMA cadeia (trocar x↔z, checar
sinais do right-hand rule no comentário da lei em `LAWS.bend:523`).

## Progresso confirmado em 22/09/2026 (sessão de retomada 2)

A sessão de 21/09 (job `4f2a7e15`) terminou e seu diretório de scratch foi
apagado — `div.bend` não existe mais. Toda a cadeia matemática do
`kickzsign` foi **reescrita do zero, provada e colada de verdade em
`PROOF.bend`** (não é mais scratch): 27 `def`s novos no fim do arquivo,
de `lt_zero_r` até `movez_idle0`. Confirmados um por um com
`bend <arquivo>.bend --check-only` isolado (< 1s cada) e depois juntos
num arquivo combinado — todos passam. `PROOF.bend` inteiro **não foi**
reverificado do zero com sucesso porque **o HEAD da branch (646f180),
sem nenhuma mudança minha, já falha** em `bend PROOF.bend --check-only`:

```
Error:
- expected : Data
- observed : Type
Location: pivota0_fs (PROOF.bend:1472-1474)
```

Reproduzido duas vezes, determinístico, na função `pivota0_fs` (nada a
ver com as leis de tombo — é código antigo, de `energy_never_grows`).
`FS(-b2: P.Body) -> Type: {...==True{}:Bool}` — um `def` que devolve
`Type`. `~/.bend/bin/bend` instalado é 2.0.24; o próprio binário avisa
"`bend 2.0.25 is available`" a cada rodada — **suspeita forte de
regressão/mudança de estrictude no kind-checker entre versões**, não um
bug de lógica da prova (o commit anterior alega "as 25 leis antigas
seguem provadas" — ou foi verificado com outra versão do `bend`, ou o
"All terms check." daquele commit não rodou até o fim). **Não investiguei
mais fundo — fora do escopo desta tarefa (leis de tombo), mas bloqueia
qualquer "All terms check." de ponta a ponta até alguém consertar ou
fixar a versão do bend.** Não tentei `bend update` (troca de versão é
uma decisão do humano, não algo para fazer sem avisar).

**Consequência prática**: todo o trabalho novo abaixo foi verificado
**isoladamente** (arquivos de scratch com import direto de `phys.bend`/
`ring.bend`, nunca o `PROOF.bend` inteiro). Está colado no fim de
`PROOF.bend` de boa fé — sintaticamente correto e tipando sozinho, mas
a frase "bend PROOF.bend deve imprimir All terms check." do AGENTS.md
**não pôde ser confirmada nesta sessão** por causa do bug acima, que já
existia antes de eu tocar em nada.

### O que está prova/pronto (27 defs, fim de PROOF.bend)

1. **Kit Nat/Z genérico** (`lt_zero_r`, `mul_pos`, `le_zero_l`,
   `le_weaken_r`, `le_weaken_s`, `le_to_lt_s`, `le_s_to_lt`, `go_mono`,
   `go_pos`, `div_pos`, `pick_n_pos`, `pick_high_1_pos`, `sub_zero_r`,
   `le_add_l`, `divc_numerator_ge`, `divc_mag_pos`) — Reusa
   `le_refl`/`clash`/`clash2` que já existem em `PROOF.bend` (não
   duplicados). Ponto alto: `go_pos`/`go_mono` provam por indução
   estrutural em `Nat.divmod.go` (o algoritmo de divisão do Base é
   "fuel"-based, recursa no primeiro argumento) que `Nat.div(a,b) > 0`
   quando `a >= b > 0` — Base não tem esse fato pronto, tive que provar
   do zero (a invariante chave: `Nat.divmod.go`'s acumulador `d` só
   cresce, `go_mono`; com fuel suficiente ele cresce pelo menos uma vez,
   `go_pos`).
2. **Kit de absorção de zero em Z** (`Z_add_r_pos0`, `Z_add_r_neg0`,
   `Z_add_l_pos0`) — a armadilha `Pos{0n}`/`Neg{0n}` do prompt anterior,
   resolvida: `Z.add(v,Neg{0n})==v` vale sempre; `Z.add(v,Pos{0n})==v`
   (e a versão à esquerda) só vale quando `v` tem magnitude conhecida
   > 0.
3. **`crz_eq`**: `Rot.crz(ax,ay,Pos{0n},Pos{g}) == Z.mul(ax,Pos{g})`
   (o termo `ay*0` sempre cancela, para qualquer sinal de `ay` —
   precisa case-split em `ay` e usar o kit de zero acima).
4. **`kickzsign`**: a lei em si, `ax * divc(crz(...), D) > 0` sempre que
   `ax≠0`, `g>0`, `D>0` — **idêntica à versão do prompt anterior**, com
   `D` genérico (não `Nat.add(8n,Y)` explícito — mais simples de usar,
   `about_pos` abaixo dá a prova de positividade de `Rot.about` de
   graça).
5. **`about_pos`**: `Rot.about(s,rx,ry,rz) > 0` sempre — trivial
   (`{==}` sozinho fecha, porque a definição começa literalmente com
   `Nat.add(8n, ...)`, e 8n já é `1n+7n`, positivo por construção).
6. **`pick_same`**: `Pick.n(c,v,v)==v` para qualquer `c` — descoberta
   nova nesta sessão (não estava nas notas de ontem), necessária porque
   `Fric.take`/`Fric.speed` (a fricção do `Body.drive`) deixam termos
   presos em `Pick.n(<condição opaca>, 0n, 0n)` quando a velocidade é
   zero — os dois ramos dão `0n`, mas o checador não resolve sozinho sem
   saber a condição.
7. **`drive_idle0`, `movex_idle0`, `movez_idle0`**: montagem mecânica —
   `Body.drive`/`Move.x`/`Move.z` são no-op (na posição/velocidade) num
   corpo em repouso (`v=0`), input parado, sem obstáculos. Precisou
   `match k: case P.K{...}:` **explícito** antes de `Body.drive`
   desenrolar — descoberta desta sessão, documentada na próxima seção.

### Armadilhas novas encontradas nesta sessão (além das do prompt de ontem)

- **A direção do `%e : P` é: `P` escrito com `_` nas posições de `b`
  (o LADO DIREITO do tipo de `e : {a==b}`), tal que `P` com `_→b`
  reconstrua o goal ATUAL; depois do rewrite o goal vira `P` com `_→a`.**
  Isso é o que o guia (`bend guide`) já diz, mas é fácil escrever ao
  contrário sem perceber — o erro que aparece (`expected`/`observed`
  trocados de um jeito estranho) não deixa óbvio qual lado está errado.
  Regra prática: se você quer ELIMINAR um subtermo travado/opaco (tipo
  `Nat.mul(a,0n)` com `a` opaco) em favor de algo mais simples (`0n`),
  o subtermo travado É o `a` do seu `e` — então use `Equal.sym` primeiro
  para inverter, e SÓ ENTÃO escreva `_` na posição dele (que virou `b`
  depois do `sym`). Se `e` já tem o termo simples como LHS e o travado
  como RHS (como `sub_zero_r`/`add_zero` quando os dois lados já
  aparecem separados no goal, um de cada lado do `==`), não precisa de
  `sym`.
- **`match` não aceita escrutinar uma variável já mencionada no tipo de
  algo anterior no bloco** ("a match on a parameter or field... give it
  its own def" / "consumed binder"). Solução: fazer o `match` na
  variável ANTES de usá-la em qualquer `%rewrite : T` ou chamada que a
  mencione no tipo — nunca depois. Achei isso em três lugares
  (`divc_numerator_ge` com `n`, `kickzsign` com `ax`, `drive_idle0` com
  `k`); sempre resolvido reordenando (match primeiro).
- **`Pick.n`/`Pick.high`/etc. de `phys.bend` precisam do prefixo `P.`**
  mesmo dentro de arquivos que já têm `import ./phys.bend as P` — chamar
  `Pick.n(...)` sem prefixo dá "expected: a defined name, observed:
  Pick.n" (o nome não resolvido é tratado como uma variável livre).
- **Definições "achatadas" (sem `match` no topo) travam em cima de uma
  variável opaca do tipo certo, mesmo sendo single-constructor.**
  `Drive.ground(k,...)` (que começa com `K{g,mu,jump,acc,size}=k`, um
  `let` desestruturante, não um `match`) NÃO desenrola sozinho quando
  `k: P.K` é uma variável universal opaca — precisa de
  `match k: case P.K{g,mu,jump,acc,size}: ...` explícito na prova para
  o checador "aprender" a forma de `k` e continuar reduzindo. Isso pegou
  `Body.drive` (via `Drive.go`→`Drive.ground`). Vale a pena checar se
  outras funções "achatadas" do `phys.bend` (sem `match` na própria
  definição, só `let`s) têm o mesmo problema quando aparecem atrás de
  uma variável opaca do tipo certo.
- **`?g` (imprime o goal) é a ferramenta mais rápida para descobrir
  exatamente onde o checador travou** — muito mais rápido que tentar
  adivinhar a forma exata do termo à mão. Fluxo usado: escrever a
  igualdade que eu acho que vale, terminar com `?g`, rodar
  `bend arquivo.bend --check-only`, ler o "expected" (é o goal real,
  todo desenrolado até onde o checador consegue ir sozinho) e escrever
  o próximo passo a partir dele — nunca tentar prever a forma reduzida
  de cabeça.
- **Nunca desenrolar a lei inteira de uma vez** — tentei rodar
  `on_a_corner_it_tips_x` completa com `?g` no topo e o "expected" saiu
  com several KB de termo (Quat.same expandido em quatro Z.same, cada
  um com Nat.cmp aninhado, tudo dentro do corpo inteiro do
  `Body.tick`). Provar em pedaços pequenos (uma função do pipeline por
  vez: `drive_idle0`, depois `movex_idle0`, etc.) e só compor no fim é
  a única forma viável.

### O que falta para fechar `on_a_corner_it_tips_x`

Com `drive_idle0` + `movex_idle0` + `movez_idle0` já prontos, o próximo
passo é montar `Body.step1` inteiro como um no-op de posição/velocidade
que só seta o giro via `Rot.held`, e daí:

1. **`step1_idle0`**: compor as três peças acima
   (`Tick.z(s,g,Pos0,Move.x(s,[],Pos0,Body.drive(...)))`) até
   `Move.y(s,g,[],corpo_pós_drive)`. `Move.y` chama `Move.ygo(s,
   Body.ground(corpo)=True{}, g,[],corpo)` → `Move.ystay` →
   `Move.stay(Geo.held(...),...)`. `Geo.held(flat,s,x,y,z,q,[]) =
   Bool.not(Tick.sinks(s,[],x,y,z,q))` — e `Tick.sinks(s,[],x,y,z,q)` é
   **exatamente** a hipótese `held` da lei (`==False{}`), então
   `Geo.held(...)=True{}` é direto (só precisa usar a hipótese, sem
   lema novo).
2. Com `Geo.held=True{}`, `Move.stay(True{},...) = Body{x,y,z,Pos0,Pos0,
   Pos0,True{},h', Rot.held(Geo.onfloor(s,y,q), rt,s,x,y,z,g,[])}` — e
   `Geo.onfloor(s,y,q)` é **exatamente** a hipótese `floor` da lei
   (`==True{}`), então `Rot.held(True{},...) = Rot.pressw(rt,s,
   Hold.low(Rot.mat(q),s),g)` — mesmo braço `Hold.low` que aparece na
   conclusão da lei, de graça.
3. Como `rt = Rot{q,Wv.zero()}` (hipótese literal da lei), `Rot.press`
   dá `Rot{q, Wv.add(Wv.zero(), Rot.kickd(D,ax,ay,az,Pos0,Pos{g},Pos0))}`
   com `(ax,ay,az)=Hold.low(Rot.mat(q),s)`, `D=Rot.about(s,ax,ay,az)`.
   `Wv.z` disso é `Z.add(Pos{0n}, Z.divc(Rot.crz(ax,ay,Pos0,Pos{g}),D))`
   — aplicar `Z_add_l_pos0` (precisa magnitude de
   `Z.divc(Rot.crz(...),D)` > 0, que sai do MESMO cálculo que
   `kickzsign` já faz por dentro — dá pra extrair um lema auxiliar tipo
   `kickzsign_ne0` ou só reusar as peças `crz_eq`+`divc_mag_pos`
   diretamente).
4. Isso dá o corpo **depois do `Body.step`** (chamem de `bf0`, com
   `Rot.w(bf0) = w'` onde `w'.z` é exatamente o termo do `kickzsign`).
   Falta ainda `Tick.spin` (que decide se entra em `Tick.turn` olhando
   `Wv.null(Rot.w(bf0))` — precisa `Wv.null(w')==False{}`, que sai de
   `kickzsign` dar `w'.z` com magnitude > 0) e, se entrar,
   `Tick.turn0`→`Tick.turn1`→`Tick.turn1b`→`Tick.turn2(held=bf0.ground=
   True{}, floor=Geo.onfloor(s,y,q)=True{} de novo)` → `Tick.pivota(...,
   Hold.low(Rot.mat(q),s))` (o MESMO braço, `Rot.mat(Rot.q(bf0))` é
   `Rot.mat(q)` porque o quatérnio não mudou) → `Tick.pivota0` →
   `Body.spin(tip,moved,bf,rt)`. Essa última parte é a "montagem
   mecânica sem matemática nova" que as notas de ontem já mapearam
   (`Tick.pivota0` ignora seu `Mat`; só importa `Tick.moved(bf,rt)`);
   ainda não escrevi em Bend, é o próximo passo real — cada `def`
   "achatado" nessa cadeia (`Tick.turn1b`, `Tick.pivota0`, etc.)
   provavelmente vai precisar do mesmo truque do `match k:` acima
   quando bater numa variável opaca (aqui, `q: P.Quat` e `s,g: Nat`
   universais da lei).

### Ordem de trabalho sugerida (revisada)

1. `step1_idle0` (os 4 passos acima, um `?g` de cada vez).
2. `Wv.null(w')==False{}` a partir de `kickzsign`'s magnitude > 0.
3. A cadeia `Tick.spin`→`Tick.pivota0`→`Body.spin`, em pedaços pequenos
   (cada função do pipeline vira seu próprio `def` provado isolado,
   como `drive_idle0`/`movex_idle0`/`movez_idle0` acima — não tente a
   lei inteira de uma vez).
4. Montar `Laws.on_a_corner_it_tips_x` juntando tudo, colar em
   `PROOF.bend` de verdade (já está lá o kit; falta só essa última
   função).
5. `on_a_corner_it_tips_z`: mesma cadeia, x↔z.
6. `past_the_edge_it_tips_*4`: mesma cadeia trocando `Hold.low` por
   `Hold.arm(Geo.foot(...))` — o braço muda, mas `kickzsign` (com `ax`
   sendo `Wv.x(Hold.arm(...))` em vez de `Wv.x(Hold.low(...))`) é
   literalmente o mesmo lema, já pronto.
7. `tipping_is_never_thrown_away_*4`: compõe `past_the_edge` com o
   argumento moved-ou-mantido de `Body.spin` (quase de graça dado 6).

**Antes de continuar**: alguém precisa decidir o que fazer sobre o bug
de `pivota0_fs` (Data vs Type) — ou fixar a versão do `bend` que
verificou o commit `646f180` originalmente, ou investigar se é uma
regressão real do compilador, ou reportar upstream. Sem isso, nenhuma
sessão futura vai conseguir ver "All terms check." do `PROOF.bend`
inteiro, mesmo terminando todas as 10 leis.
