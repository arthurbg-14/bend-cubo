# Cubo Azul

Um jogo 3D em [Bend 2](https://github.com/bendlang/bend): você é o **cubo
azul**. Anda, pula, **empurra os cubos verdes** e **sobe neles**. Os cubos
verdes nascem ao acaso (uma semente nova a cada partida), em pilhas de 1 a 3,
num mundo **sem fim**: meio milhão de quilômetros para cada lado.

A física segue as leis da cinemática, da conservação da energia e do atrito
de Coulomb, e isso é **provado**. São treze leis em [`LAWS.bend`](LAWS.bend),
e `bend PROOF.bend` só passa se todas valem. Elas valem para **qualquer valor
das constantes**, e isso importa porque gravidade, atrito, pulo e motor mudam
durante o jogo.

A GPU desenha (Vulkan); o Bend simula.

![subindo nos cubos](docs/jogo.png)
![empurrando](docs/cubos.png)

## Jogar

```sh
./build.sh      # checa PROOF.bend, depois compila ./cubo
./cubo
```

| tecla | ação |
|---|---|
| W A S D | andar (para onde a câmera olha) |
| Espaço | pular (segurado, pula de novo ao tocar o chão) |
| mouse | girar a câmera |
| roda | aproximar / afastar a câmera |
| Tab, ↑ ↓, 1 … 6 | escolher uma constante |
| ← → | mudar a constante escolhida (segurar repete) |
| R | constantes de volta ao padrão |
| Enter | voltar ao início |
| N | mundo novo (outra semente) |
| H | mostrar / esconder as teclas |
| Esc | sair |

Para empurrar, é só andar contra um cubo verde. Ele sai com a sua velocidade
dividida entre os dois (a colisão conserva o momento) e desliza até o atrito
pará-lo. Empurra também uma fila inteira. Um pulo sobe 1,5 m com as
constantes padrão, o bastante para subir num cubo de 1 m e, dali, numa pilha
de 2. Tire um cubo de baixo de uma pilha e os de cima caem.

`./cubo demo` joga sozinho (W segurado, um pulo a cada 1,5 s, a câmera
girando). `./cubo still` usa a semente fixa 12345, sem nada se mover, para
medir.

Precisa de Linux com X11 (XWayland serve), clang e um driver Vulkan (Mesa
RADV/ANV ou o do fabricante; a `libvulkan` é carregada na execução). O
`build.sh` recompila o shader com `glslc` se houver; senão usa o SPIR-V já
embutido em `effs/screen.c`.

### As constantes

Todas mudam durante o jogo; o painel mostra o valor em unidades físicas.

| constante | padrão | passo | o que é |
|---|---|---|---|
| Gravidade | 9,75 m/s² | 0,5 | a velocidade que a gravidade tira a cada tick |
| Atrito do chão | µ 0,80 | 0,05 | Coulomb: o chão freia µ·g (a força normal é m·g); 0,80 é borracha em asfalto seco |
| Pulo | 5,41 m/s | 0,25 | a velocidade de saída; o painel mostra a altura que a energia dá, J²/2g |
| Força no chão | 20 m/s² | 1 | o empurrão do "motor" ao andar |
| Força no ar | 4 m/s² | 1 | o controle no ar |
| Vel. máxima | 6 m/s | 0,5 | até onde o motor acelera |

O painel mostra também, a cada frame, a altura, a velocidade e a **energia
mecânica** do cubo azul em J/kg. Num pulo ela fica parada enquanto ele voa.

## As leis

Em [`LAWS.bend`](LAWS.bend), provadas em [`PROOF.bend`](PROOF.bend). Cada lei
é sobre o tick de verdade do jogo, `Body.tick` (o mesmo que o jogo roda), e
vale para qualquer corpo, qualquer conjunto de obstáculos em volta e
qualquer valor de todas as constantes. Algumas pedem "sem entrada"; outras
pedem "sem contato", um tick em que nenhum portão de colisão barrou o
movimento. O tick marca isso no próprio corpo (`hit`).

| lei | o que garante |
|---|---|
| `free_flight_energy` | no ar, sem entrada e sem contato, a energia mecânica (cinética + potencial) é **exatamente** a mesma depois do tick |
| `free_flight_kinematics` | o mesmo tick é movimento uniformemente acelerado: `v' = v − g`, a horizontal não muda (sem atrito no ar), e cada coordenada anda `v + v'` (a velocidade média) |
| `flight_is_parabola` | um voo inteiro, de qualquer duração e com quaisquer obstáculos em volta, é **exatamente** a parábola da física real: depois de n ticks (t = n/128 s), `v = v₀ − a·t`, `y = y₀ + v₀·t − ½·a·t²` e `x = x₀ + vₓ·t`, com a = g/8 m/s² (9,75 m/s² no padrão), sem erro que se acumule |
| `jump_energy` | um pulo sem contato dá ao corpo **exatamente** `J²` de energia vertical; somada a `free_flight_energy`, a altura do pulo é a da conservação da energia |
| `no_air_jump` | no ar, segurar o pulo não muda nada (pular exige apoio) |
| `friction_never_reverses` | no chão, sem entrada, o atrito só freia: nenhum componente da velocidade cresce ou troca de sentido |
| `coulomb_friction` | o atrito de um tick tem módulo no máximo µ·g, em qualquer direção de deslize: `fx² + fz² ≤ (µg)²` |
| `friction_work` | teorema trabalho-energia: a energia cinética perdida é **exatamente** o atrito vezes a distância deslizada, e o corpo desliza essa distância |
| `rest_stays` | atrito estático: um corpo parado no chão ou em cima de um cubo, sem entrada, fica exatamente onde está |
| `push_momentum` | uma colisão (o empurrão) **conserva o momento** exatamente |
| `push_energy` | uma colisão nunca cria energia cinética |
| `energy_never_grows` | sem entrada, nenhum tick aumenta a energia do corpo mais a dos obstáculos que ele toca; só o motor e o pulo põem energia |
| `no_clip` | um corpo livre dos obstáculos continua livre depois do tick, com qualquer entrada: nada anda, cai ou é empurrado para dentro de outro cubo |

Não há `@unsafe`, `?TODO` nem axiomas. A verificação leva cerca de 10 s.

### Por que a energia fecha exatamente

Tudo é inteiro. Um tick dura 1/128 s. Posições estão em 2⁻¹⁸ m (um cubo tem
2¹⁸ unidades) e velocidades em 1/1024 m/s. Com essa escolha, uma velocidade
`v` anda `v` unidades em meio tick, e o tick move o corpo `v + v'`: a
velocidade do começo mais a do fim, que é a velocidade média. Com aceleração
constante isso é a integração **exata**, sem erro de passo. Sob gravidade `g`:

    v' = v − g,   Δy = v + v'   ⟹   v'² − v² = −g·(v + v') = −g·Δy

logo `v² + g·y` não muda de tick para tick. Essa é a energia mecânica, em
J/kg vezes 2²¹. O jogo não arredonda nada no voo, e a lei confirma isso
exatamente. O mesmo vale para o atrito: `v² − v'² = f·(v + v')`, a energia
perdida é a força vezes a distância.

Somando os ticks, n deles andam `2n·v₀ − g·n²` unidades, que em metros são
`v₀·t − ½·a·t²` com t = n/128 s e a = g/8 m/s². É a queda livre da física,
e a lei `flight_is_parabola` prova isso para um voo de qualquer duração.
Também foi medido no jogo rodando, pelo relógio: com as constantes padrão, um
pulo ficou 1102 ms no ar (141 ticks) e subiu 1,502 m. Na Terra, com
9,75 m/s², um pulo de 1,50 m dura 2·√(2·1,5/9,75) = 1,109 s. O laço de frames
roda 128,3 ticks por segundo de relógio.

### Como foram provadas

- **Uma tática de anel provada.** O Bend não tem táticas, e uma identidade
  polinomial se prova reescrevendo passo a passo. [`ring.bend`](ring.bend)
  resolve isso por reflexão:
  1. uma expressão vira sintaxe (`Ex`);
  2. `norm` a leva a uma soma canônica de monômios;
  3. `norm_ok` prova que `norm` preserva o valor;
  4. duas expressões com a mesma forma normal têm o mesmo valor (`Ring.eq`),
     e o checador calcula a forma normal sozinho.

  Todas as contas de energia (as quatro fases de um tick de gravidade, pouso,
  atrito, colisões) usam isso.
- **Caracterizar o caminho livre.** Um tick que termina sem contato passou
  pelo ramo livre de todos os portões, porque o contato, uma vez marcado,
  nunca é desmarcado dentro do tick. Os lemas `x_air_eq`/`x_gnd_eq` mostram
  que o corpo final é o da fórmula do movimento livre, e as leis de energia e
  cinemática viram contas sobre essa fórmula.
- **Portões.** Cada decisão do código é um `Bool` passado a um helper; cada
  lema quantifica sobre esse `Bool` e recebe como ele foi calculado. Os
  portões de colisão, a raiz quadrada do atrito (checada: `s² ≥ a² + b²`) e a
  divisão da colisão (checada: `d = e + e + j`) são verificados no próprio
  código. Assim as provas dependem de fatos que o código garante, não da
  correção de uma divisão ou de uma raiz.
- **Indução sobre os ticks.** `flight_is_parabola` junta a lei de um tick
  com o resto do voo. Para a altura, a identidade G = D + B + (2m+1)·A sai
  pela tática de anel, e o que os dois lados têm em comum se cancela.
- **Indução sobre os obstáculos.** O empurrão procura o primeiro obstáculo
  atingido numa lista qualquer. `energy_never_grows` e `no_clip` são provadas
  por indução nessa lista: o empurrão muda velocidades, nunca posições.
- **O tamanho do cubo é uma constante como as outras** (`K.size`). As leis
  valem para qualquer tamanho, e o checador nunca expande o número 262144 em
  unário.

### As leis bloqueiam bugs

Três bugs plausíveis, cada um numa cópia do projeto. Cada um compila
(`bend phys.bend` imprime "All terms check."), mas `bend PROOF.bend` falha:

| bug introduzido | onde a prova quebra |
|---|---|
| subir com `Δy = 2v` em vez de `v + v'` | `fly_up_e` (`free_flight_energy`) |
| atrito de 2µg, sem o portão de Coulomb | `take_le` (`coulomb_friction`, `friction_work`) |
| colisão que devolve 1 unidade a mais ao que empurra | `same_chk_mom` (`push_momentum`) |

## Arquitetura

    phys.bend     a física provada: números com sinal, constantes, corpo,
                  atrito, motor, colisão (divisão de momento), movimentos com
                  portões, gravidade, o tick
    ring.bend     a tática de anel: lemas de Nat, normalizador, prova de correção
    LAWS.bend     as leis          PROOF.bend   as provas
    world.bend    o mundo: gerador por hash, trie das células mudadas, vizinhança
                  de um corpo, cubos acordados e dormindo, o tick do mundo
                  (blocos coloridos em paralelo para muitos cubos; a octree
                  para cubos rapidíssimos)
    clash.bend    o teste de colisão (./build.sh test)
    main.bend     o jogo: entrada, câmera, constantes, HUD, o laço de frames
    bench.bend    benchmark sem janela
    effs/         scene.comp.in: o shader (raios, sombras, HUD); screen.c: Vulkan,
                  a tabela de células mudadas da GPU, os eventos da janela;
                  font.glsl: a fonte do HUD (tools/font.py); spv.sh: shader → SPIR-V
    tools/        font.py (fonte 8×16 Latin-1); order.py (ordena os defs de um
                  arquivo .bend: cada um depois dos que usa)

- **O mundo infinito.** Cada célula de 1 m tem, por um hash da semente, 0 a 3
  cubos empilhados. A densidade varia por região (2 % a 17 %), e em volta do
  início não há nada. O mundo gerado não ocupa memória: uma trie guarda só as
  células que mudaram (um cubo que saiu, um que parou ali), e o resto lê o
  gerador. As posições são `Nat`, e o início fica em 2⁴⁷ unidades, ou 2²⁹ m,
  de cada borda.
- **Dormindo e acordado.** Um cubo parado dorme na sua célula e não custa
  nada. Empurrado, ou sem apoio porque o de baixo saiu, acorda: sai da
  célula, e os que estavam em cima dele acordam também. Um cubo acordado é
  simulado entre os corpos ao seu alcance até parar no chão ou sobre cubos
  dormindo, e então volta a dormir.
- **A vizinhança exata.** Um corpo só pode tocar, num tick, o que está a
  menos de um cubo e do quanto ele anda nesse tick (`W.reach`). A simulação
  consulta só as células desse alcance (em geral 3×3) e só os corpos
  acordados dentro dele. Os de longe passam intactos.
- **Muitos cubos: blocos coloridos, em paralelo.** Com poucos acordados
  (menos de 128), cada um olha os outros diretamente. Com muitos:
  - **Os blocos.** O chão é dividido em blocos de 4×4 m, e cada bloco ganha
    uma de 4 cores, pela paridade do x e do z (um xadrez 2×2). Dois blocos
    da mesma cor têm um bloco inteiro entre eles. Esses 4 m são mais que um
    cubo mais duas vezes o que qualquer coisa alcança num tick, então os
    cubos de dois blocos da mesma cor nunca tocam o mesmo corpo.
  - **As 4 fases.** O tick roda uma fase por cor. Em cada fase, todos os
    blocos daquela cor rodam ao mesmo tempo, e cada um roda seus cubos em
    ordem, entre os cubos dos 8 blocos em volta (parados nessa fase) e os
    cubos dormindo. Cada cubo roda uma vez por tick, na fase do seu bloco.
  - **A árvore.** Os blocos ficam numa árvore espacial que corta um bit de
    cada vez, do mais alto para o mais baixo, x e z alternados: é a octree
    sem os cortes em y, porque os cubos ficam perto do chão. A árvore é
    montada a cada tick por partição radix, as duas metades em paralelo, e
    as fases a percorrem com um fork em cada nó (`a b = f(x) g(y)`).
  - **Tudo no mesmo tick.** O jogador olha só os 9 blocos em volta dele. Um
    cubo dormindo que leva um empurrão acorda no fim do tick (até lá, quem o
    toca já o vê andando). Cada bloco decide em paralelo quais dos seus
    cubos param, e as células são gravadas depois, uma a uma.
  - **A octree.** Se algo alcança mais de 1 m num tick (acima de ~120 m/s),
    a separação dos blocos não vale, e o tick usa a octree: a caixa dos
    cubos cortada ao meio, com os cubos que atravessam o corte rodando
    depois dos dois lados.

  As células mudadas ficam numa trie rasa, pelos 8 bits baixos de cada
  eixo (a de 30 níveis era metade do tempo), e cada bloco lê as células da
  sua região uma vez por tick.

  `./build.sh test` derruba 432 cubos uns sobre os outros por 300 ticks e
  confere, a cada tick, que nenhum entra em outro e que nenhum some. Roda o
  mesmo cenário pela lista, pela octree, pelos blocos e pela mistura que o
  jogo usa.
- **Na GPU**, um compute shader em cinco passes por frame:
  1. monta uma grade 256×256 em volta do jogador, já com o gerador calculado;
  2. marca as células mudadas, lidas de uma tabela de hash que o `screen.c`
     mantém a partir dos "remendos" que o Bend manda;
  3. insere os corpos em movimento;
  4. põe a câmera atrás do jogador, sem atravessar cubos;
  5. lança um raio por pixel: DDA 2D pelas células, a pilha gerada de cada
     uma e os cubos que alcançam a célula; depois sombra (um segundo raio
     para o sol), contato no chão, neblina e o texto do HUD.

  O gerador é o mesmo hash do Bend, então o mundo intocado não precisa ser
  enviado.

## Desempenho

AMD Ryzen 7 5700U com a Radeon integrada (Vega 8, RADV), 1280×720:

| | |
|---|---|
| GPU, cena parada (`./cubo still`) | 1,91 ms/frame (~450 fps) |
| GPU, jogando (`./cubo demo`) | 1,5–2,3 ms/frame (330–550 fps) |
| um tick de um corpo entre 10 obstáculos (`Body.tick`) | 0,79 µs |
| tick do mundo andando e empurrando | 22 µs, ou ~0,3 % de um núcleo a 128 ticks/s |
| tick do mundo com 64 cubos caindo e se empilhando | 0,65 ms |
| tick do mundo com 1024 cubos caindo ao mesmo tempo (blocos) | ~6 ms |
| cabeçalho de um frame (câmera, corpos, HUD) | 33 µs |

`./build.sh bench && ./bench` roda esses cenários sem janela.

**Quantos cubos se mexendo ao mesmo tempo.** Medido com cubos caindo, todos
acordados. As três versões rodaram alternadas, na mesma máquina, com outros
processos usando ~4 núcleos (CPU a ~95 °C):

| cubos | cada um olhava todos | octree | blocos coloridos |
|---|---|---|---|
| 256 | 6,9 ms/tick | 3,4 ms/tick | 2,3 ms/tick |
| 1024 | 87 ms/tick | 9,5 ms/tick | 5,7 ms/tick |
| 2025 | — | 16,8 ms/tick | 10,0 ms/tick |
| 4096 | 2994 ms/tick | 31,6 ms/tick | 17,0 ms/tick |

O tempo real pede 7,8 ms por tick (128 por segundo), então cabem ~1400 cubos
se mexendo ao mesmo tempo; eram ~256 com cada cubo olhando todos. Com mais,
a simulação continua certa, só anda mais devagar que o relógio: com 4096,
na metade da velocidade. Um cubo parado não custa nada, e o mundo tem
quantos cubos parados couberem nele.

A GPU desenha no máximo 250 cubos em movimento de uma vez, o jogador
incluído. Os outros aparecem quando param.

Cada passo foi medido antes e depois (`./bench`, `perf`, e o tempo de GPU que
o HUD mostra):

| mudança | antes | depois |
|---|---|---|
| gerador calculado uma vez por célula por frame, na grade; altura máxima da cena medida por frame (raios de céu e de sombra param cedo) | 8,86 ms de GPU | 3,72 |
| contagem de cubos na mesma palavra da célula (uma leitura por passo do raio) | 2,14 | 1,91 |
| vizinhança pelo alcance exato (3×3 em vez de 5×5) e só os corpos acordados ao alcance | 187 ms (walk) / 194 ms (rain) | 130 / 98 |
| checagem de sono só para cubos já parados (`Bool.and` do Bend avalia os dois lados) | 130 / 98 | 96 / 75 |
| linhas fixas do HUD reescritas só quando mudam | 90 µs/frame | 31 |
| cubos acordados numa octree em paralelo, em vez de cada um varrer todos (O(N²)) | 1024 cubos: 87 ms/tick | 11,8 |
| células dos cubos dormindo lidas uma vez por nó da octree, e não por cubo | 1024 cubos: 11,8 ms/tick | 8,6 |
| blocos coloridos: 4 fases, cada uma com todos os blocos de uma cor em paralelo (a octree deixava 47% dos cubos nos cortes, em sequência) | 4096 cubos: 31 ms/tick | 19 |
| trie das células com 8 níveis em vez de 30; vizinhos filtrados pelo alcance do bloco; o que mudou no vizinho anotado a cada passo, sem reordenar | 4096 cubos: 19 ms/tick | 16–17 |
