# Tarefa: física de corpo rígido de verdade, com leis gerais (23/09/2026)

## Por quê

O motor antigo (phys.bend) não é física de corpo rígido: "em pé" é um
bit (`ground`) que desliga a gravidade quando o corpo "não consegue
descer" (`Tick.sinks`), os movimentos são um eixo de cada vez com
portões, o empurrão divide a velocidade num eixo só (sem giro) e o tombo
é uma busca de pivô à parte. Toda lei provada era sobre essa colcha, e
cada uma tinha uma saída:

- `standing_is_held` só pede "não desce mais uma unidade": uma parede do
  lado satisfaz, e o jogador fica em pé no ar segurando uma direção.
- `past_the_edge_it_tips` e `tipping_is_never_thrown_away` pedem giro,
  não movimento: um cubo que nunca vira as satisfaz.
- Nada fala do mundo (world.bend): quem dorme, quem vê quem. O sono pedia
  só "tem cubo embaixo" (`Geo.rests`), e um cubo com o meio para fora da
  borda dormia ali para sempre.

Medido (tmp/diag/stress.bend, 6 mundos x 4000 ticks, entrada como a do
usuário): o jogador ficou pendurado no ar em todos os mundos (até 2592
ticks seguidos) e "em pé em cima de nada" em todos. Um cubo batido
rápido nunca sai girando.

## O modelo

Cada corpo é um cubo rígido de massa 1 e lado s: posição (canto, como
hoje; centro = canto + s/2), orientação (quatérnio em 2^-15), velocidade
linear v e **momento angular** L (por unidade de massa, em unidades de
posição x velocidade, exato: um impulso J num braço r soma r x J). A
inércia de um cubo é I = s^2/6, então w = 6 L / s^2.

O tick do mundo, sobre a ilha (corpos acordados + os que dormem
encostados neles):

1. Forças: gravidade v_y -= g em todo corpo. Motor e pulo do jogador só
   com apoio embaixo (contato de normal para cima no tick anterior).
2. Contatos: vértice-contra-face entre cada par próximo (os 8 cantos de
   A dentro da caixa de B aumentada de uma margem, e vice-versa) e contra
   o chão. Cada contato: ponto, normal da face (unitária em 2^-16),
   folga (gap).
3. Impulsos sequenciais (N iterações): em cada contato, o impulso normal
   que faz a velocidade relativa no ponto (v + w x r) não fechar mais que
   a folga, acumulado e nunca negativo (contato só empurra); o atrito,
   contra a velocidade tangencial, com |J_t| <= mu J_n (Coulomb). O
   impulso é aplicado igual e oposto nos dois corpos, no mesmo ponto:
   v_a += J, L_a += r_a x J, v_b -= J, L_b -= r_b x J.
4. Integração: corpo sem contato nenhum anda a parábola exata de hoje
   (x += v + v', giro livre); corpo com contato anda x += 2 v'. Cada
   corpo só vai para uma pose livre de todos os outros e do chão; se não
   cabe, a maior fração que cabe (bissecção), senão fica (e perde a
   velocidade: uma batida).
5. Repouso: um corpo com velocidade e giro residuais pequenos cujo meio
   está sobre o polígono dos apoios fica exatamente parado. Só um corpo
   exatamente parado, reto, apoiado e equilibrado pode dormir.

Tombar da borda, sair girando de uma batida fora do meio, escorregar,
cair de uma parede: nada disso é regra própria. É o que os impulsos nos
pontos de contato fazem.

## As leis (propostas; o humano aprova)

Gerais, sobre o tick do mundo inteiro, não sobre um passo do código:

1. **Voo livre** (ficam): energia, cinemática, parábola exata, giro livre.
2. **Ação e reação**: todo impulso de contato entre dois corpos é igual e
   oposto e aplicado no mesmo ponto: o momento linear e o angular do par
   (em torno de qualquer ponto) não mudam. Só o chão, a gravidade e o
   jogador mudam o momento total.
3. **Contato só empurra**: o impulso normal de todo contato é >= 0.
4. **Coulomb**: em todo contato, |atrito| <= mu x normal.
5. **A energia nunca cresce**: sem entrada, a energia mecânica total
   (translação + rotação + potencial) depois do tick é no máximo a de
   antes.
6. **Nada atravessa nada**: se nenhum par de corpos se sobrepõe antes do
   tick do mundo, nenhum se sobrepõe depois (o mundo, não um corpo).
7. **Nada flutua**: um corpo sem contato nenhum perde exatamente g de
   velocidade vertical; parede não segura (o contato só empurra ao longo
   da normal, e o atrito é limitado por Coulomb).
8. **Repouso é equilíbrio**: um corpo que o tick deixa exatamente parado
   tem apoio embaixo e o meio sobre ele.
9. **Dormir não muda nada**: o mundo só põe para dormir um corpo que o
   tick deixaria exatamente como está.

## Fases

1. Motor novo em `rigid.bend` (ao lado de phys.bend) + testes sem tela:
   cubo parado no chão, pilha de 3, cubo com o meio fora da borda tomba e
   deita, batida fora do meio gira, jogador contra a parede cai, nenhuma
   sobreposição, nada pendurado. Aceitação: stress.bend com 0 em tudo.
2. O mundo (world.bend) passa a ticar ilhas com o motor novo; sono e
   despertar pela lei 9; main.bend.
3. LAWS.bend novo + PROOF.bend: as leis acima, provadas.
4. Desempenho (bench, cem) e a GPU.

## Estado (23/09/2026)

Fases 1 e 2 feitas: o jogo roda `rigid.bend`, ilha por ilha
(`world.bend`, `W.tick`). Medido sem janela (tmp de trabalho: stress,
rtest, ptest, chuva):

- 6 mundos x 4000 ticks com o jogador andando e pulando ao acaso: nenhuma
  sobreposição; parado no ar no máximo 2 ticks seguidos (o motor antigo:
  até 2592).
- cenários: parado no chão, queda de 1 m, pilha de 3, meio para fora da
  borda (tomba e deita reto), batida fora do meio (gira), apertado contra
  a parede no ar (cai), inclinado 30 graus (deita reto).
- 64 cubos jogados se empilham e dormem todos em 3 s; 27 inclinados em
  pilha se acomodam e param.
- `./build.sh test`: as nove linhas OK, a do jogo com a medida do motor
  novo (sobreposição = mais fundo que o slop, R.hits).

O que cada caso ensinou (tudo geral, nada de caso especial):

- apoio é contato que toca (folga até o slop do mais baixo que empurrou),
  com a face olhando para cima, empurrando: aresta e cunha contam, parede não;
- o giro zero não mexe na orientação (renormalizar girava o cubo 1/2^15);
- a correção do pivô compara o braço ida-e-volta com ele mesmo;
- aresta com aresta gera contato quando separa o par melhor que as faces;
- sem o giro, antes de fracionar o movimento; quem só cabe 1/8 para;
- ilhas: cruzar ilhas refaz o tick como uma; o dorminhoco empurrado acorda
  e se mexe no mesmo tick; a ilha dorme inteira, girada como está.

Falta: fase 3 (LAWS.bend das leis gerais acima, provadas).
