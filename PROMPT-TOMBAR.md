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
