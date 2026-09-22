# Tarefa: as 10 leis que faltam depois do conserto do tombo (21/09/2026)

> **Estado atual (22/09/2026, fim do dia): 27 de 35 provadas.**
> `on_a_corner_it_tips_x` e `_z` fechadas. Faltam 8:
> `past_the_edge_it_tips_{px,nx,pz,nz}` e
> `tipping_is_never_thrown_away_{px,nx,pz,nz}`. Leia a ÚLTIMA seção deste
> arquivo ("Sessão de 22/09/2026 (parte 3)") antes de tudo — as seções
> do meio registram becos sem saída já descartados.

## Estado (21/09, histórico)

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

## Sessão de 22/09/2026: o bug era nosso, não do compilador, e a técnica
## para compor o "encaixe mecânico" (resolvido)

**O bug do `pivota0_fs` acima era real, mas não é do `bend`** (testado em
2.0.24 E 2.0.25, idêntico nos dois — não é regressão de versão).
`pivota0_fs`/`pivota0_nc` tinham um parâmetro `FS(...)`/`FREE(...)`
(devolve `Type`, ver `def FS(...) -> Type:`) marcado `+` (reuso), mas
`+` exige `Data` (`bend guide`: "Reusable variables require Data"), e as
outras seis funções irmãs (`put_fs`, `place_fs`, `pivot_fs`, `pivota_fs`,
`turn2_fs`, `keepw_fs`'s `hb`) nunca marcam um parâmetro `FS(...)`/
`FREE(...)` com `+` — só a versão *crua* do predicado (`{...==True{}:
Bool}`, que É `Data`) quando precisa ser reusada. Corrigido em `_fs`/`_nc`
trocando o tipo do parâmetro para a forma crua (como `cand_fs`/`shrink_fs`/
`start_fs` já faziam); em `_fl`/`_sh` só faltava o `+` (o tipo já era cru).
`bend PROOF.bend` inteiro agora atravessa o arquivo e para exatamente em
"10 TODOs found" — as 10 leis do tombo, nada mais quebrado. Rodar isso
ainda leva ~alguns minutos (busca de giro do `Tick.shrink`, documentado
acima) — **não repita esse full-run a cada edição pequena**, é exatamente
o erro que essa sessão cometeu no começo (quatro full-runs de ~40min só
para achar esse bug, um por família `_fs`/`_nc`/`_fl`/`_sh` — dava para
ter lido o código das seis famílias de uma vez e comparado).

### A técnica que faltava: `Equal.cong` + `Equal.trans`, não `%e : T` direto no `Body.step`

O `?g`/`%drive_idle0(...) : T` direto em cima de `Tick.body(Body.step(k,
...))` (k opaco) **não funciona** — o checador, ao comparar `T` com o
goal, deixa `Body.drive(k,...)` se expandir sozinho (via `Drive.go`/
`Drive.ground`) numa expressão gigante e ilegível (`Pick.n(Cmp.is_le(...),
0n,0n)` por todo canto, da fricção não simplificada) **antes** de eu
conseguir escrever `T` certo — tentar adivinhar essa forma expandida à
mão (mesmo copiando do "expected" do erro) é uma armadilha: `match k:
case P.K{...}:` no topo da prova NÃO evita isso, só faz a expansão
acontecer com os campos de `k` nomeados em vez de projeções — o problema
nunca foi opacidade de `k`.

**A saída**: construir a igualdade por congruência, functor de cada vez,
sem nunca deixar o checador normalizar o `Body.step(k,...)` inteiro:

```
Equal.cong(A, B, f, a, b, e)   -- e : {a==b:A}  dá  {f(a)==f(b):B}
Equal.trans(A, a, b, c, ab, bc) -- ab:{a==b}, bc:{b==c}  dá  {a==c}
```

Para cada passo do pipeline (`Body.drive` → `Move.x` → `Tick.z`/`Move.z`
→ `Tick.body`/`Move.y`), envolva o fato já provado (`drive_idle0`,
`movex_idle0`, `movez_idle0`, `movey_stay0`) com `Equal.cong` usando uma
LAMBDA como `f` (ex.: `(b: P.Body) => P.Move.x(s, [], P.Pos{0n}, b)`) e
encadeie com `Equal.trans` — cada perna intermediária ou é um `cong` de
um lema já prontoou é `{==}` puro (quando os dois lados de uma perna são
literalmente a mesma forma reduzida, tipo `Tick.z(s,g,v,(bd,[]))` contra
`Tick.y(s,g,Move.z(s,[],v,bd))`, que são iguais por definição, sem
precisar de lema nenhum). O checador nunca precisa expandir
`Body.drive(k,...)` sozinho — cada `cong`/`trans` só compara as formas
que EU escrevi, todas curtas. Isso desbloqueou `step_body` (o `Body.step`
inteiro, parado, idle, sem obstáculo, vira o corpo com o giro trocado por
`Rot.pressw(...)`) e `step_pair` (a mesma coisa, mas o par
`Body&List<&2,Body>` inteiro, para alimentar `Tick.spin`/`Tick.moved`
depois) — ambos provados e colados em `PROOF.bend`.

**Duas armadilhas de sintaxe que custaram tempo**:
- `+x = Rot{...}` (um `let` que CONSTRÓI um record, não desestrutura)
  falha com "an annotated term (cannot infer)" — Bend consegue *checar*
  `Rot{...}` contra um tipo esperado, mas não consegue *sintetizar* o
  tipo de um construtor sozinho fora de um `let` sem anotação. A anotação
  é `{expr : T}` (chaves), **não** `(expr : T)` (parênteses — isso é só
  para operadores `+ - * /` sobre `T`). `+rt = {P.Rot{q, P.Wv.zero()} :
  P.Rot}` resolve.
- Direção do `%e : T` (para quem for usar de novo): dado `e : {a==b:T}`,
  escreva `T` = "o goal atual com uma ocorrência de `b` marcada `_`" —
  **`b` precisa já aparecer no goal**, sintaticamente, antes da reescrita
  (não `a`). Quando o que está preso no goal é `a` (ex.: uma hipótese
  `h: {Tick.sinks(...)==False{}}` e o goal tem `Bool.not(Tick.sinks(...))`
  — `Tick.sinks(...)` É o `a`, não o `b`), inverta primeiro com
  `Equal.sym(T, a, b, e) : {b==a:T}` e marque a NOVA posição de `b`
  (que agora é o lado direito do sym, i.e. o `a` original) — ver
  `Z_add_r_pos0`/`movey_stay0` como referência. Errar a direção não dá
  erro de sintaxe, dá um "expected/observed" gigante e ilegível (o
  checador tenta normalizar o goal inteiro para comparar) — se isso
  acontecer, suspeite da direção antes de qualquer outra coisa.

### O que está provado agora (além do `kickzsign` de ontem)

Tudo em `PROOF.bend`, verificado isolado num `scratch_corner.bend`
(apagado ao final, não commitado — recrie a partir do bloco entre
`lt_zero_r` e `wv_null_false_z` em `PROOF.bend` se precisar iterar de
novo rápido) antes de colar:

- `wz_after_pressw`/`wz_after_pressw0`: `Wv.z(Rot.w(Rot.pressw(rt,s,a,g)))
  == Z.add(Wv.z(Rot.w(rt)), Z.divc(Rot.crz(Wv.x(a),Wv.y(a),Pos0,Pos{g}),
  Rot.about(s,...)))` — puro `{==}`, sem match nenhum (record achatado
  reduz livre quando não precisa decidir um Bool).
- `movey_stay0`: `Move.y` de um corpo parado, idle, sem obstáculo, dadas
  `held`/`floor`, vira o corpo com `Rot.pressw(rt,s,Hold.low(Rot.mat(q),
  s),g)` no lugar do giro.
- `step_body`/`step_pair`: o `Body.step` inteiro (drive+movex+movez+
  movey), mesma hipótese, monta o resultado acima — a peça que a
  PROMPT-TOMBAR de ontem apontava como "o próximo passo real".
- `wz_step`: compõe `step_body` com `wz_after_pressw0` — dá `Wv.z(Rot.w(
  Body.rot(Tick.body(Body.step(...)))))` já na forma que o `kickzsign` de
  ontem espera.
- `kickzsign_mag`/`wv_null_false_z`/`and_false_r`/`lt_neq0`: a magnitude
  do `w'.z` é positiva (extraído do meio da prova do `kickzsign`, mesma
  ideia) e isso basta para `Wv.null(w')==False{}` (só o componente z
  importa, `Wv.null` é um `Bool.and` de três `is_eq(mag,0)`).

### Próximo passo exato para fechar `Laws.on_a_corner_it_tips_x`

Falta só a "montagem mecânica" que a sessão de ontem já tinha mapeado por
leitura de código (sem matemática nova), agora com a técnica de
`Equal.cong`/`Equal.trans` para não travar em `Tick.shrink`/`Tick.cand`
opacos. `Body.tick(k,[],idle,B0) = Tick.spin(s,g,Body.step(k,[],idle,
B0))`, `Tick.spin(s,g,r)=(Tick.turn(s,g,obs,b),obs)` com `(b,obs)=r` —
usar `step_pair` (o resultado já é um par LITERAL `(FINAL_BODY,[])`, que
destroi direto) para chegar em `Tick.turn(s,g,[],FINAL_BODY)`.

1. `Tick.turn(s,g,[],FINAL_BODY) = Tick.turn0(s,g,[],FINAL_BODY)` (`obs=[]`,
   caso direto) `= Tick.turn1(Wv.null(Rot.w(Body.rot(FINAL_BODY))),...)`.
   `Body.rot(FINAL_BODY) = Rot.pressw(rt,s,a,g)` direto (projeção do
   record que `step_body`/`step_pair` já constroem), então
   `Wv.null(Rot.w(Rot.pressw(rt,s,a,g)))==False{}` sai direto de
   `wz_after_pressw0` + `kickzsign_mag` + `Z_add_l_pos0` (magnitude) +
   `wv_null_false_z` — vale a pena empacotar isso num lema
   `wv_null_pressw(q,s,a,g,...)` antes de `wz_step` (não precisa do
   `Tick.body(Body.step(...))` por fora, `Body.rot(FINAL_BODY)` já É
   `Rot.pressw(...)` direto).
2. `Tick.turn1(False{},...) = Tick.turn1b(s,g,[],FINAL_BODY)` (caso
   direto). `Tick.turn1b` destrói `FINAL_BODY` (literal) e chama
   `Tick.turn2(gr=True{}, Geo.onfloor(s,y,Rot.q(Rot.pressw(...))), ...,
   Rot.pressw(...), Rot.free(Rot.pressw(...)), MAT_OPACO)`.
   `Rot.q(Rot.pressw(rt,s,a,g))=q` direto (`Rot.press` só mexe no `w`) —
   `Geo.onfloor(s,y,q)` é EXATAMENTE a hipótese `floor` de novo. `MAT_OPACO`
   nunca precisa ser calculado (ver abaixo).
3. `Tick.turn2(True{},True{},...)` cai no caso `True{} True{}`:
   `Tick.pivota(md,s,g,[],x,y,z,Pos0,Pos0,Pos0,True{},True{},rt2,r2,
   Hold.low(Rot.mat(Rot.q(rt2)),s))` com `rt2=Rot.pressw(...)` — o braço
   aqui é de novo `Hold.low(Rot.mat(q),s)` (mesmo `a` de sempre, já que
   `Rot.q(rt2)=q`). **`md` nunca é usado por `Tick.pivota0`** (confirmado
   por leitura: `Tick.pivota0(md,...)` não referencia `md` no corpo) —
   não perca tempo calculando o `Rot.mat(Quat.half(Quat.step(...)))` que
   `Tick.turn1b` monta pra ele, o valor passa por `Equal.cong`/`Equal.trans`
   como um termo opaco de tipo `P.Mat`, sem nunca ser avaliado.
4. `Tick.pivota(md,s,g,[],...) = Tick.pivota0(md,s,g,[],...)` (`obs=[]`,
   caso direto). `Tick.pivota0` desmonta `a=Wv{ax,ay,az}`, monta
   `w2=Tick.boost(...)`, `b0=Tick.cand(...)`, `bf=Tick.shrink(7n,
   Tick.moved(b0,rt2),b0,...)`, e devolve `Body.spin(tip, Tick.moved(bf,
   rt2), bf, rt2)` com `tip=Nat.is_lt(0n,Nat.add(mag(ax),mag(az)))`.
   `tip=True{}` sai de `off` via `lt_add` (já no kit: `lt_add(mag(ax),
   mag(az), off) : {0 < mag(ax)+mag(az)}`).
5. **Não dá pra evitar nomear `b0`/`bf` por extenso** (são termos
   concretos, não hipóteses) — mas como em nenhum ponto abaixo o valor de
   `bf` é realmente inspecionado (só `Tick.moved(bf,rt2)` como Bool, e
   `Rot.q(bf)`/`Body.setrot(bf,...)` tratados opacos), o `match
   Tick.moved(bf,rt2):` de baixo é o único lugar que realmente decide
   algo — os termos `w2`, `b0`, `bf` só precisam ser escritos (copiados
   de `Tick.pivota0`'s corpo em `phys.bend`), nunca avaliados.
6. `match Tick.moved(bf,rt2):`
   - `case True{}`: `Body.spin(tip,True{},bf,rt2)=bf` (`Body.spin`'s
     próprio `match moved: case True{}: b`, direto). O primeiro
     disjunto da lei é `Bool.not(Quat.same(Rot.q(Body.rot(a_final)),q))`
     — com `a_final=bf` aqui e `Rot.q(rt2)=q`, isso é `Tick.moved(bf,
     rt2)` **por definição** (`Tick.moved(b,rt)=Bool.not(Quat.same(
     Rot.q(Body.rot(b)),Rot.q(rt)))`) — que já é `True{}` (hipótese do
     `case`). De graça, `Bool.or(True{},_)=True{}` fecha (usar
     `or_here`, já no kit).
   - `case False{}`: `Body.spin(True{},False{},bf,rt2) = Body.setrot(bf,
     Rot{Rot.q(bf),Pick.w(True{},Rot.w(rt2),Wv.zero())}) = Body.setrot(
     bf,Rot{Rot.q(bf),Rot.w(rt2)})` (`Pick.w(True{},a,b)=a`, direto).
     `Rot.w(Body.rot(Body.setrot(bf,R)))=Rot.w(R)=Rot.w(rt2)` (`Body.setrot`
     só troca o campo `rot`, `Rot.w` projeta o record literal `R` que EU
     construí). Então `Wv.z(Rot.w(a_final))=Wv.z(Rot.w(rt2))` — que
     `wz_after_pressw0`/`wz_step` já calculam. Fechar com `kickzsign`
     (que dá `Z.mul(ax,Z.divc(...)) above Pos0`) + `Z_add_l_pos0` (pra
     absorver o `Z.add(Pos0,·)` que sobra, usando `kickzsign_mag` pra
     magnitude ≠0) — o segundo disjunto da lei
     (`Z.above(Z.mul(Wv.x(a),Wv.z(w')),Pos0)`) fecha com `or_there`
     (já no kit).
7. Montar `Laws.on_a_corner_it_tips_x(k,heavy,x,y,z,h,q,floor,held,off)`
   juntando 1-6 via `Equal.cong`/`Equal.trans` (cada passo acima vira uma
   perna do encadeamento, igual `step_body` fez) + o `match` final do
   passo 6. Rodar `bend PROOF.bend` inteiro só no final, uma vez.

Depois disso: `on_a_corner_it_tips_z` é a MESMA cadeia trocando x↔z
(checar sinal do right-hand-rule no comentário da lei, `LAWS.bend:523`);
`past_the_edge_it_tips_*4` troca `Hold.low(Rot.mat(q),s)` por
`Hold.arm(Geo.foot(...),Rot.mat(q),s)` — o `kickzsign`/`kickzsign_mag`
já são genéricos em `ax`/`ay` (não sabem de onde o braço veio), só a
"montagem mecânica" (passos 1-3 acima) muda de forma (o `held=False`/
`floor=True` branch de `Tick.turn2` vira `held=True,floor=False`, usa
`Hold.arm` em vez de `Hold.low`) — precisa também fixar o sinal do braço
via `Geo.leanf` usando a hipótese `past`, ainda não derivado.
`tipping_is_never_thrown_away_*4` compõe `past_the_edge` com o mesmo
argumento moved-ou-mantido do passo 6 acima.

## Sessão de 22/09/2026 (parte 2): `{==}` explode em cima de
## `Tick.turn1b`/`Tick.pivota0`/`Tick.shrink` — a técnica certa é a mesma
## do `_fs` (casar por parâmetro, nunca comparar por igualdade)

**Achado crítico, custou muitas iterações**: qualquer `{==}` (ou
`Equal.cong`/`Equal.trans`, que por baixo também é `{==}`) que compare
algo contra `Tick.turn1b(...)`/`Tick.turn2(...)`/`Tick.pivota(...)`/
`Tick.pivota0(...)` **trava** (não erra, trava — CPU alto, RAM baixa e
estável, sem terminar em minutos) — **mesmo para reflexividade trivial
`X==X` com o `X` literalmente idêntico dos dois lados**. Reproduzido
isolado (arquivos de uma função só): `{P.Tick.turn1(False{}, s, g, [], b)
== P.Tick.turn1(False{}, s, g, [], b) : P.Body}` prova por `{==}` TRAVA
quando `b` é uma chamada de função (`Corner.body2(x,y,z,q)`) em vez de um
parâmetro puro — porque para checar `{==}`, o `bend` parece normalizar o
termo por completo, e `Tick.turn1b` puxa `Tick.turn2`→`Tick.pivota`→
`Tick.pivota0`→`Tick.shrink` (recursão de 7 níveis, cada um com um
`Tick.cand`→`Tick.pivot`→`Tick.place`→`Tick.put`→`Tick.drop` — mais
64 passos de bisseção lá dentro) — para `x,y,z,q,s` opacos isso é
literalmente a mesma explosão que o comentário do `Tick.drop` em
`phys.bend` já avisa ("a mesma lema levou mais de dois minutos em vez de
cinco segundos" quando desenrolado sem cuidado) — só que pior, porque meu
caso não tinha CUIDADO NENHUM.

**A técnica que já funciona no arquivo (família `_fs`/`_nc`/`_fl`/`_sh`,
todas já provadas) nunca usa `{==}` perto dessa recursão.** Ela usa
CASAMENTO POR PARÂMETRO: uma função cujo TIPO DE RETORNO já menciona o
parâmetro que vai ser casado (`keepw_fs(...) -> FS(P.Body.spin(tip,
moved, b, rt))`, com `moved` sendo o PRÓPRIO parâmetro que o `match
moved:` decide) — o checador ESPECIALIZA o tipo esperado sozinho, em
cada ramo do `match`, com UM PASSO de redução (a própria definição de
`Body.spin`, que NÃO é recursiva) — nunca precisa normalizar
`Tick.shrink`/`Tick.pivota0` por dentro. Reproduzi essa técnica do zero
para uma propriedade nova (o sinal do giro, não a `FS`/`FREE` antigas) e
funcionou RÁPIDO:

```
def WZ(+q: P.Quat, +ax: P.Z, +rt: P.Rot, -b: P.Body) -> Type:
  {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(b)), q)),
    P.Z.above(P.Z.mul(ax, P.Wv.z(P.Rot.w(P.Body.rot(b)))), P.Pos{0n})) == True{} : Bool}

def spin_wz(moved: Bool, +ax: P.Z, +q: P.Quat, +rt: P.Rot, +b: P.Body,
  hmoved: {moved == Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(b)), q)) : Bool},
  hw: {P.Z.above(P.Z.mul(ax, P.Wv.z(P.Rot.w(rt))), P.Pos{0n}) == True{} : Bool})
  -> WZ(q, ax, rt, P.Body.spin(True{}, moved, b, rt)):
  match moved:
    case True{}:
      or_here(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(b)), q)), P.Z.above(P.Z.mul(ax, P.Wv.z(P.Rot.w(P.Body.rot(b)))), P.Pos{0n}),
        Equal.sym(Bool, True{}, Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(b)), q)), hmoved))
    case False{}:
      or_there(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(b)), q)), P.Z.above(P.Z.mul(ax, P.Wv.z(P.Rot.w(rt))), P.Pos{0n}), hw)
```
(`WZ` já é a conclusão da lei inteira, `Bool.or(não-mudou-quatérnio,
sinal-certo)`; `tip` fica travado em `True{}` porque na lei ele sempre é
— `off` implica `tip` via `lt_add`, ver abaixo. `or_here`/`or_there`
provam `Bool.or` a partir de um dos dois lados, já no kit.) **Verificado
isolado, rápido (segundos), sem travar** — a peça que faltava desde a
parte 1 desta sessão.

`pivota0_wz` (compor `spin_wz` com o `Tick.pivota0` de verdade, mesma
estrutura de `+w2`/`+b0`/`+bf` que `pivota0_fs` já usa) **não fecha — e
agora está isolado O PORQUÊ, com evidência, não só suspeita**:

**Diagnóstico confirmado por teste diferencial.** Escrevi `WZ2`/
`keepw_wz2`/`pivota0_wz2` — CÓPIA BYTE-A-BYTE da estrutura de
`pivota0_fs` (mesmos `+heavy`/`+f`, mesma forma inline sem `+b0`/`+bf`,
mesma recursão), só trocando o predicado `FS` por um IGUALMENTE simples
que eu escrevi (`Bool.or(Nat.is_lt(0n,Z.neg(vy)),ground)` — só
`Body.vy`/`Body.ground`, sem tocar rotação). **Isso ficou pequeno e
estável (~100-150MB, oscilando, nunca passou de 160MB em 2 minutos)** —
igual a `pivota0_fs` isolada (testada à parte: ~150-170MB por 12 minutos
inteiros, terminando ou não, mas NUNCA explodindo). Troquei só o
predicado de volta pro `WZ` real (que projeta `Rot.q(Body.rot(b))` e
`Rot.w(Body.rot(b))`) mantendo TUDO o resto idêntico (testei com
`+b0`/`+bf` como lets reusáveis, sem eles/inline, com `obs` genérico e
com `obs:=[]` fixo — quatro variações) — **todas as quatro explodiram**:
RAM saindo de ~130MB pra 1.3GB pra 2.7GB em 30-40 segundos (tive que
matar na mão duas vezes, uma quase esgotou a RAM da máquina inteira,
14GB usados/300MB livres — mate rápido se isso acontecer de novo, não
deixe rodar "só mais um pouco").

**Conclusão: não é a técnica de prova (casar por parâmetro está
certa — `WZ2` prova isso), é o PREDICADO.** `Rot.q`/`Rot.w` de um corpo
que veio da busca do `Tick.shrink` força o checker a avaliar a
ARITMÉTICA DE QUATÉRNIO INTEIRA (`Quat.step`/`Rot.turn`, multiplicações
repetidas de `Z` — Pos/Neg envolvendo Nats) atravessando os até 7 níveis
da busca, pra só então extrair um campo do quatérnio final — isso é uma
EXPLOSÃO DE TERMO genuína (provavelmente exponencial no número de
níveis), não um bug de como a prova foi escrita. `FS`/`WZ2` só olham
`vy`/`ground`, que `Body.spin` (e a cadeia toda: `Tick.put`→`Tick.letv`/
`Tick.stands`) parecem deixar baratos de extrair mesmo vindos da busca —
só o quatérnio é caro.

```
-- variação que EXPLODIU (uma das quatro testadas, a mais próxima de
-- pivota0_fs -- as outras três variam só obs genérico/fixo e lets vs
-- inline, todas com o mesmo resultado):
def pivota0_wz(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +q: P.Quat, +rt: P.Rot, +r2: P.Rot, a: P.Wv,
  +off: {Nat.is_lt(0n, P.Z.mag(P.Wv.x(a))) == True{} : Bool},
  hrt: {P.Rot.q(rt) == q : P.Quat},
  hw: {P.Z.above(P.Z.mul(P.Wv.x(a), P.Wv.z(P.Rot.w(rt))), P.Pos{0n}) == True{} : Bool})
  -> WZ(q, P.Wv.x(a), rt, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)):
  P.Wv{+ax, +ay, +az} = a
  +w2 = P.Tick.boost(Nat.is_le(Nat.div(s, 32n), Nat.add(P.Z.mag(ax), P.Z.mag(az))), P.Rot.w(rt))
  spin_wz(
    P.Tick.moved(P.Tick.shrink(7n, P.Tick.moved(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt),
    ax, q, rt,
    P.Tick.shrink(7n, P.Tick.moved(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az),
    {==}, hw)
```
`WZ`/`spin_wz` (a parte 2 acima) continuam corretas e ficam no kit —
`spin_wz` sozinha (com `b`/`moved` como parâmetros abertos, nunca
derivados de `Tick.pivota0`) é rápida e útil; o problema é só na
COMPOSIÇÃO com a busca de verdade.

### O problema real a resolver (não é mais "achar a técnica", é isto)

Preciso de um jeito de saber o SINAL de `Wv.z(Rot.w(a_final))` **sem
pedir pro checker extrair `Rot.q`/`Rot.w` de um corpo que atravessou
`Tick.shrink`**. Duas direções possíveis, nenhuma tentada ainda:

1. **Provar a invariante SOBRE `Rot.w`, não sobre o corpo inteiro,
   ANTES da busca decidir nada — como uma equação, não como um campo
   extraído.** A busca (`Tick.shrink`/`Tick.cand`/`Tick.pivot`) SÓ MEXE
   no quatérnio `q` (via `Rot.turn`) — o giro (`Rot.w`) nunca muda
   durante a busca (`Tick.cand` monta `Rot{Rot.turn(Rot.q(rt),w),
   Rot.w(rt)}` — o `Rot.w(rt)` original, intacto, em TODO candidato).
   Então `Rot.w(Body.rot(bf)) == Rot.w(rt)` deveria valer
   INCONDICIONALMENTE, ANTES de saber se `moved` é True ou False — se
   eu conseguir provar ISSO (uma equação sobre `Rot.w` apenas, LIVRE do
   quatérnio) por indução em `n` do jeito que `shrink_fs` faz (recursão
   estrutural em `n`, nunca `{==}` contra o resultado cheio), talvez
   `Rot.w` fique tão barato de extrair quanto `vy`/`ground` — porque a
   prova nunca PRECISA olhar pro quatérnio, só pro `Wv` que nunca é
   tocado. Vale a pena tentar um `shrink_rotw`/`cand_rotw` mirror da
   família `_fs`, com um predicado `ROTW(+w0: Wv, -b: Body) -> Type:
   {Wv.same(Rot.w(Body.rot(b)), w0) == True{} : Bool}` (ou até
   `Rot.w(Body.rot(b)) == w0` direto, se `Wv` permitir `{==}` estrutural
   sem cair na mesma armadilha — testar pequeno primeiro).
2. **Achar se existe uma versão "opaca" de `Tick.pivota0` que devolve
   o giro e o quatérnio SEPARADOS** (ou construir uma) — se o giro
   nunca muda na busca, pode dar pra reescrever a lei usando uma função
   auxiliar que só devolve `Rot.w`, sem nunca materializar o quatérnio
   final — mas isso mexe em `phys.bend`, não é só prova, então é uma
   mudança maior (parar e perguntar antes).

Ambas ainda precisam ser tentadas isoladas (arquivo pequeno,
`bend --check-only`, nunca `PROOF.bend` inteiro) com monitoramento de
RSS (a forma seca que funcionou nesta sessão:
```
BPID=$(nohup bend arquivo.bend --check-only > out.txt 2>&1 & echo $!)
# then poll: ps -o rss= -p $BPID, matar se passar de ~2GB
```
) — **nunca deixe um `bend --check-only` novo rodar sem monitorar RSS
depois do que aconteceu nesta sessão** (chegou a 14GB usados / <300MB
livres na máquina inteira uma vez, por eu não ter monitorado rápido o
suficiente).

### Próximo passo exato (revisado de novo)

1. Tentar a direção 1 acima (`ROTW`/`shrink_rotw` — giro é invariante da
   busca, provar por indução em `n`, nunca por igualdade contra o
   resultado cheio). Se isso ficar barato (Rot.w SEM precisar do
   quatérnio), o resto do plano das sessões anteriores (turn1b_wz,
   turn0_wz, compor com step_pair/wz_step) segue igual, só trocando
   `spin_wz`/`WZ` pra usar esse fato em vez de reconstruir `Rot.w` via
   `Tick.pivota0` inteiro.
2. Se a direção 1 também esbarrar em custo (o quatérnio pode aparecer
   em outro lugar que eu não previ), considerar a direção 2 — mas essa
   é uma decisão de escopo maior (mexe em `phys.bend`), não decidir
   sozinho, perguntar antes.
3. Uma vez resolvido o sinal do giro sem tocar o quatérnio: `turn1b_wz`
   (`Tick.turn2` caso `True,True`, braço `Hold.low(Rot.mat(q),s)`),
   `turn0_wz` (`Wv.null`, já pronto em `wv_null_pressw`), compor com
   `step_pair`/`wz_step` (RASO, já funciona) → `Laws.on_a_corner_it_tips_x`.
4. Depois: `on_a_corner_it_tips_z` (espelha x↔z), `past_the_edge_it_tips_*4`
   (troca `Hold.low` por `Hold.arm(Geo.foot(...))`), `tipping_is_never_
   thrown_away_*4` (compõe com o argumento moved-ou-mantido).

## Sessão de 22/09/2026 (parte 3): o giro atravessa a busca intacto (`ROTW`) — quina fechada

**O que destravou tudo**: a busca do giro (`Tick.shrink`→`Tick.cand`→
`Tick.pivot`→`Tick.place`→`Tick.put`) **nunca mexe em `Rot.w`** — todo
candidato é `Rot{Rot.turn(q,w), Rot.w(rt)}` e `Tick.put` devolve ou ele ou o
`rt` original. Então o predicado certo não é o da lei (que projeta
`Rot.q`, o quatérnio — explode), é `ROTW(w0, b) = {Rot.w(Body.rot(b)) ==
w0}`, provado por indução espelhando a família `_fs` (`put_rotw` …
`shrink_rotw`/`start_rotw` … `pivota0_rotw`/`pivota_rotw`/`turn2_rotw`/
`turn1b_rotw`/`turn1_rotw`/`turn0_rotw`/`turn_rotw`). Checa em ~2 min,
~150MB. Bônus: como o giro final é SEMPRE `Rot.w(rt2)` (nos dois ramos de
`moved`, e nos dois de `Wv.null` — por isso `wv_null_false_z` & cia eram
desnecessários e foram apagados), o SEGUNDO disjuntor da lei vale
incondicionalmente: `or_there` + o sinal do `kickzsign`, sem casar em
`moved` nenhum.

Em `PROOF.bend` (fim do arquivo): família `ROTW`, `corner_spin` (o giro
depois de um tique inteiro = `Rot.w(rt2)`), `corner_sign_x`/`_z` (sinal do
chute, só da prensa), `kickxsign`/`kickxsign_mag`/`crx_eq`/`Z_add_l_neg0`/
`Z_opp_mul_pos_mag`/`wx_after_pressw0`/`lt_add_r` (o espelho do eixo x), e
`Laws.on_a_corner_it_tips_x`/`_z`. Verificado isolado (arquivo com o kit +
tudo isso importando `LAWS.bend`: "33 TODOs found" = 35 − 2, nada mais).
**A rodada completa de `bend PROOF.bend` NÃO foi feita no commit** (~50 min,
o usuário pediu pra pular) — rode uma antes de mexer mais; o esperado é
"8 TODOs found".

Armadilhas desta parte: `+x = {...}` só com anotação em chaves; nunca `+` em
let/parâmetro cujo tipo é `ROTW(...)`/`FS(...)` (devolvem `Type`, `+` exige
`Data`) — só na forma crua `{a==b:T}`; `match b: case Body{...}` precisa dos
campos marcados `+` se forem usados mais de uma vez; não dá pra casar duas
vezes o mesmo parâmetro em ramos aninhados (use `%Equal.sym(...,h) : T`
pra reescrever); e a direção do `%e : T` continua sendo a fonte nº 1 de erro
(o `_` marca o lado da equação que JÁ está no goal — quase sempre precisa
`Equal.sym` por fora).

**Nunca rode `bend` sem vigiar RSS** (a combinação que funcionou):
`nohup nice -n 19 bend X.bend --check-only > out 2>&1 &` e um laço
`ps -o rss= -p $PID`, matando acima de ~2.5GB. Uma variante sem vigia chegou
a 8GB e quase derrubou a máquina.

### As 8 que faltam — o que já está derivado

**`tipping_is_never_thrown_away_*`** (4): mesma forma da quina — `Body.tick`,
giro inicial zero, conclusão `Bool.or(quatérnio mudou, sinal)`. Reaproveita
`corner_spin` quase inteiro, com duas diferenças: (1) `obs = [o]` em vez de
`[]`, então `step_pair` precisa de uma versão com um obstáculo (ver abaixo);
(2) o ramo de `Tick.turn2` é `held=True, floor=False` (`off` aqui é
`onfloor == False`) — `turn2_rotw` hoje exige `hfloor: floor == True`;
precisa de uma variante (ou generalizar) que, no caso `True False`, chame
`pivota_rotw` com `Hold.arm(Geo.foot(...))` e o `htip` do braço-arm. O sinal
vem do braço (abaixo), não do `Hold.low`.

**`past_the_edge_it_tips_*`** (4): só `Body.step` (sem busca — `ROTW` nem
entra), `obs = [o]`, `rt` ARBITRÁRIO (giro inicial qualquer). Conclusão: o
passo diminui/aumenta `Wv.z` (ou `Wv.x`) do giro. Cadeia:
1. `Rot.held(False, …) = Rot.pressw(rt, s, Hold.arm(Geo.foot(s,x,y,z,q,[o],
   Foot.none()), Rot.mat(q), s), g)` — o ramo sem chão (`off`).
2. `Geo.foot(…,[o],Foot.none()) = Geo.foot1(s,dx,dz,x,y,z,o,Foot.none())`,
   que devolve `Foot{1, laplw, laphw, …}` se `under'` (uma versão com
   `lapd`, a sombra) ou `Foot.none()` senão. **Não precisa decidir qual**:
   casar no Bool e tratar os dois.
3. Sinal do braço (px): `arm.x = Geo.leanf(h, a, LX, HX)` com `h = s/2`;
   `p = max(min(a,HX),LX)` e `arm.x = Neg{h-p}` se `p < h`. Com `past`
   (`ox+s < x+h`): `HX = laphw < h` (o `min(x+s+dx, ox+s) ≤ ox+s < x+h`),
   `LX = laplw = 0` (pois `ox < x`), e no pé vazio `LX=HX=0` — em todos os
   casos `p < h`, logo `arm.x` estritamente negativo. **Atenção**: precisa
   `h > 0`, e isso sai de `across`+`past` juntos (`across` dá `x < ox+s`,
   `past` dá `ox+s < x+h`, logo `h > 0`) — para `s ≤ 1` as hipóteses se
   contradizem e a lei vale por vacuidade. `under`/`along` não entram no
   sinal.
4. Com `arm.x = Neg{m}`, `m>0`: `crz = Neg{m·g}` (via `crz_eq`), `divc =
   Neg{N}`, `N>0` (`divc_mag_pos`), e `w'.z = Z.add(w.z, Neg{N})`. Falta um
   lema `Z.above(v, Z.add(v, Neg{N})) == True` para `N>0` e `v` QUALQUER
   (`Pos{m}` com `m<N` → `Neg{N-m}`; `m≥N` → `Pos{m-N}`; `Neg{m}` →
   `Neg{m+N}`) — cuidado com `Pos0`/`Neg0` (ver topo).
5. **Aberto**: os movimentos x/z com `[o]` e velocidade zero. `Move.x` com
   `d = Pos0` cai em `Move.xok` (corpo em `x+0`) se `Geo.free(s,x,y,z,q,[o])`,
   ou em `Move.xno`→`xreach`→`xtouch`, que pode chamar `Push.x` no `o`. Os
   lemas atuais (`movex_idle0`/`movez_idle0`) são só para `[]`. Precisa
   mostrar que nos dois ramos `x` fica `x` e `obs` fica `[o]` (ou pelo menos
   que o `Rot.held` do fim vê a mesma coisa) — `Geo.free` do corpo parado
   sobre `o` não é óbvio de provar; tratar os dois ramos é mais seguro.
   Os pares nx/pz/nz espelham (nx: `past` do outro lado, sinal oposto; pz/nz:
   eixo z, `crx`, sinais do right-hand rule — igual `_x`/`_z` da quina).
