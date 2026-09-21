# Tarefa: rotação e queda de corpo rígido no Cubo Azul, com as leis provadas

## Contexto

Repositório: `~/src/bend-cubo` (branch `master`, remoto `git@github.com:arthurbg-14/bend-cubo.git`).
Jogo 3D escrito em **Bend 2** (`~/.bend/bin/bend`, sempre com `BEND_NO_TELEMETRY=1`).
Física em inteiros exatos: 1 m = 2^18, tick = 1/128 s, velocidade em 1/1024 m/s.
`./build.sh` checa `PROOF.bend` (todas as leis) e só então compila `./cubo`.
`./build.sh test` roda 11 verificações; `./build.sh chunks` o motor paralelo;
`./build.sh cem` mede 100 489 cubos por 64 ticks.
Nada entra sem `bend PROOF.bend` imprimindo "All terms check." e sem os testes verdes.

## O que está errado hoje (apagar)

Hoje **não existe rotação**. Um cubo é uma caixa alinhada aos eixos e é
"segurado" por qualquer sobreposição, então ele fica pendurado na quina de
outro. Para tapar isso foi posto um **escorregão** (`P.Slip.go`, `Geo.holds`,
`Geo.sup`, `Geo.off`, `Geo.slip1`, `W.slipped`, e as leis `no_slip_when_held`
e `slip_makes_no_energy`): o cubo com o meio fora do apoio anda de lado até
cair. **Isso é uma muleta e deve ser removido por inteiro.** Tombar não é uma
regra à parte: é consequência do torque da gravidade quando o centro de massa
sai do polígono de apoio. Quem implementar rotação de verdade apaga tudo isso.

Também já foi tentado e revertido: desenhar só o cubo azul girando enquanto a
colisão continuava alinhada. Ficou visivelmente quebrado. **Nada de meia
rotação, e nada de física diferente para o cubo do jogador.**

## O que fazer

Corpo rígido de verdade, igual para todos os cubos.

### Estado de cada corpo
- `c`: posição do **centro de massa** (hoje o código guarda o canto; mudar).
- `v`: velocidade linear.
- `R`: orientação (matriz 3×3 ortonormal ou quaternion).
- `w`: velocidade angular, no referencial do mundo.
- massa `m` (ajustável para o cubo azul, como constante do jogo).

### Inércia
Para um **cubo**, o tensor de inércia é isotrópico: `I = (m s² / 6) · Id`.
Duas consequências que simplificam tudo e devem ser usadas:
1. `I` não depende da orientação — não é preciso girar o tensor.
2. No voo livre não há precessão (`w × I w = 0`), então **`w` é constante e o
   ângulo cresce linearmente com o tempo**. O voo girando é exato, como o voo
   sob gravidade já é uma parábola exata.

### Integração de um tick (dt = 1/128 s)
- `v += g·dt` ; `c += v·dt`
- `R = rot(w·dt) · R` ; `w` só muda por impulso de contato.

### Contato e colisão
- Detecção entre caixas **orientadas** (OBB), pelo teorema do eixo separador:
  15 eixos (3 + 3 + 9 produtos vetoriais). Sai daí: ponto de contato `p`,
  normal `n`, penetração `d`.
- Resposta por impulso, perfeitamente inelástico (o resto do jogo já é):
  com `r = p − c`, a velocidade do ponto de contato é `v + w × r`;
  o impulso `J n` que anula a velocidade relativa normal é
  `J = −v_rel·n / (1/m_a + 1/m_b + n·((r_a×n)/I_a)×r_a + n·((r_b×n)/I_b)×r_b)`.
  Aplicar `v += J n/m` e **`w += (r × J n)/I`**.
- Atrito de Coulomb no contato: impulso tangencial limitado por `µ·J`, com a
  mesma constante `mu` que já existe.
- Empilhamento estável precisa de mais de um contato por corpo resolvido em
  conjunto (iteração sequencial de impulsos, várias passadas por tick) e de
  correção de penetração que **não injete energia** (Baumgarte com limite, ou
  separação posicional pura).

### Tombamento
Não escrever regra nenhuma para isso. Com contatos e impulsos corretos, um
cubo cujo centro de massa passa da aresta de apoio ganha torque de gravidade
sobre essa aresta e tomba sozinho. O teste de aceitação abaixo é justamente
esse.

## A decisão difícil: exatidão

Rotação por ângulo arbitrário **não cabe em inteiros exatos** (seno e cosseno
são irracionais). O projeto inteiro é construído sobre aritmética exata com
leis provadas, então essa decisão tem que ser tomada de propósito e escrita no
README. Três caminhos:

- **A. Ponto fixo com trigonometria tabelada.** É o que fazem os motores de
  verdade. As leis deixam de ser igualdades e passam a ser **limites**: "a
  energia não cresce mais que ε por tick", "o momento angular se conserva a
  menos de ε", com ε declarado e provado. Recomendado.
- **B. Orientações em múltiplos de 90° (24 poses) com tombo animado.** Exato
  em repouso (o cubo alinhado continua sendo uma caixa alinhada, e a colisão
  segue barata), aproximação só durante o tombo. Mantém a exatidão onde ela é
  visível, mas não dá giro livre no ar.
- **C. Matrizes de rotação racionais (transformada de Cayley).** Exato de
  verdade, mas os denominadores crescem e estouram o `Nat` de 48 bits do Bend
  em poucos ticks. Só serve com renormalização, que quebra a exatidão de novo.

Escolher A ou B, dizer qual e por quê no README, e ajustar o enunciado das
leis de acordo. Não fingir exatidão que não existe.

## Leis a provar (em `LAWS.bend`, provas em `PROOF.bend`)

1. `free_spin_is_exact` — sem contato, `w` não muda e o ângulo depois de n
   ticks é `n·w` (para um cubo não há precessão).
2. `hit_gives_angular_momentum` — um impulso `J` aplicado em `r` muda o
   momento angular em exatamente `r × J` (ou dentro de ε, no caminho A).
3. `no_spin_from_the_middle` — impulso em cheio no centro (`r = 0`) não gira.
4. `energy_never_grows` — reescrever a lei que já existe incluindo a energia
   de rotação `½ I w²`: nenhum tick sem entrada aumenta a soma de translação
   + rotação + potencial.
5. `momentum_in_a_hit` — o momento linear se conserva numa colisão (a lei
   atual `push_momentum` tem que valer com massas diferentes).
6. `topple_from_torque` — um corpo apoiado cujo centro de massa está fora do
   polígono de apoio tem torque resultante não nulo sobre a aresta de apoio.
7. `rest_is_stable` — com o centro de massa dentro do polígono, o torque
   resultante é zero e o corpo não se mexe (substitui `rest_stays`).
8. `no_clip` — reescrita para caixas orientadas.

## Testes de aceitação

Escrever como programas no repositório, rodados por `./build.sh test`:

- **Giro livre**: cubo solto com `w` dado; depois de 256 ticks o ângulo bate
  com `256·w` e a energia é a mesma do começo.
- **Quina**: cubo apoiado com 51% do apoio fica parado e dorme; com 49% tomba,
  gira sobre a aresta e cai; em nenhum tick há sobreposição.
- **Batida de quina**: cubo a 10 m/s contra a quina de outro sai girando; o
  momento angular medido antes e depois bate com `r × J`.
- **Pilha**: três cubos empilhados alinhados ficam em pé, param e dormem (sem
  tremer e sem afundar).
- **Regressão**: as 9 variantes de `./build.sh test` seguem com 0
  sobreposições e conservação exata da contagem de cubos.
- **Desempenho**: `./build.sh cem` continua rodando 100 489 cubos a 64 ticks
  por segundo ou mais (hoje: ~15,4 ms por tick com a máquina fria). Medir A/B
  intercalado — o notebook estrangula acima de 90 °C e número isolado não vale.

## Armadilhas do Bend 2 (para não perder horas)

- Sem recursão mútua. `match` só em parâmetro e antes de qualquer `let`. `def`
  tem que vir antes do uso. Não dá para destruturar valor computado.
- O checador avalia `Nat` em unário: **nunca** deixar literal grande dentro de
  função que as provas normalizam (`Nat.div(n, 32768n)` numa lei trava o
  checador). `U32` é avaliado bit a bit; `U32.from_nat` de valor simbólico
  estoura a pilha.
- Reescrita nas provas: `%e : T`, com `_` em `T` marcando onde está o lado
  esquerdo de `e`; use `Equal.sym` para inverter o sentido.
- `Array<U32>` é de dono único. Os corpos são empacotados em **6 palavras**
  (`F.put`/`F.get` em `world.bend`); com orientação e velocidade angular vão
  para ~12, e isso atinge o caminho de array único, o motor em chunks (que
  ordena por célula) e o cabeçalho da GPU. Planeje esse empacotamento antes.
- A GPU (`effs/scene.comp.in`) desenha caixas por DDA; com orientação o teste
  de interseção tem que entrar no referencial do cubo. O cabeçalho do frame
  tem 4 palavras por corpo móvel (limite de 250) — a orientação precisa caber
  ali ou o cabeçalho muda.
- Em shell de fundo use `/bin/cp -f` (o `cp` do zsh é interativo e trava).

## Ordem de trabalho

Cada passo termina com `./build.sh test` verde e um commit. Não empilhar dois
passos sem testar.

1. Apagar o escorregão e suas leis.
2. Corpo rígido no `phys.bend`: centro de massa, orientação, `w`, inércia
   isotrópica, integração livre + lei 1.
3. Empacotamento novo dos corpos em `world.bend` (array único, chunks) e
   cabeçalho/shader desenhando orientado.
4. Colisão OBB (SAT) no lugar da alinhada, com `no_clip` provado de novo.
5. Impulsos com braço de alavanca e atrito de contato: leis 2, 3, 5.
6. Contatos múltiplos, repouso estável e dormir: leis 6, 7 e o teste da pilha.
7. Energia com rotação: lei 4.
8. Desempenho: voltar aos 100 mil cubos a 64 ticks/s.
