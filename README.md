# TFT Bot
A discord bot for various TFT shenanigans.

### @TFTBot -h
```
@TFTBot -h
usage: @TFTBot [-h] [--mode {max-traits,max-non-unique-traits}] [-n [0-16]]
               [-s [0-5]] [-l CHAMP] [-p] [-c [CHAMP NAMES ...]]
               [-t [TRAITS ...]] [-b [TRAIT NAMES ...]] [--list-champs]
               [--list-traits] [--examples]

options:
  -h, --help            show this help message and exit
  --mode {max-traits,max-non-unique-traits}, -m {max-traits,max-non-unique-traits}
  -n [0-16], --num-champs [0-16]
                        Number of champs in your comp
  -s [0-5], --spatulas [0-5]
                        Specify the number of spatulas
  -l CHAMP, --headliner CHAMP
                        Specify the champ that must be my headliner
  -p, --multi-talented  Use flag if the double headliner trait portal is
                        active
  -c [CHAMP NAMES ...], --champs [CHAMP NAMES ...]
                        Champs that must be in your comp
  -t [TRAITS ...], --traits [TRAITS ...]
                        Traits that must be in your comp (example usage: -t
                        Jazz 4 Emo 2)
  -b [TRAIT NAMES ...], --blacklist-champs [TRAIT NAMES ...]
                        Champs that must not be in your comp
  --list-champs         List all possible champ names
  --list-traits         List all possible trait names
  --examples            List some example usages

Use `@TFTBot --examples` for some ideas.
```

### @TFTBot --examples
```
examples:
  **NOTE: All messages must start by tagging @TFTBot.**

  That's Jazz, Baby - output a comp with Jazz 4 enabled, at most 5 champions on my board, with the max possible non-unique traits turned on:
  `--num-champs 5 -t Jazz 4 -m max-non-unique-traits`
  
  
  ... and I also have 2 spatulas to use:
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2`
  
  
  ... and it's a multi-talent game (double headliner trait):
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2 --multi-talented`
  
  
  ... and I want Jhin and Qiyana on my team:
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2 --multi-talented -c Jhin Qiyana`
  
  
  ... and I don't want Miss Fortune or Vex on my team:
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2 --multi-talented -c Jhin Qiyana -b MissFortune Vex`
  
  I don't know the names of all champs or traits:
  `--list-champs --list-traits`
```

### @TFTBot --list-champs --list-traits
```
Champs: Ahri, Akali-KDA, Akali-TD, Amumu, Annie, Aphelios, Bard, Blitzcrank, Caitlyn, Corki, Ekko, Evelynn, Ezreal, Garen, Gnar, Gragas, Illaoi, Jax, Jhin, Jinx, KSante, KaiSa, Karthus, Katarina, Kayle, Kayn, Kennen, Lillia, Lucian, Lulu, Lux, MissFortune, Mordekaiser, Nami, Neeko, Olaf, Pantheon, Poppy, Qiyana, Riven, Samira, Senna, Seraphine, Sett, Sona, TahmKench, Taric, Thresh, Twisted, Twitch, Urgot, Vex, Vi, Viego, Yasuo, Yone, Yorick, Zac, Zed, Ziggs
Traits: 8-bit, BigShot, Breakout, Bruiser, Country, CrowdDiver, Dazzler, Disco, EDM, Edgelord, Emo, Executioner, Guardian, Heartsteel, Hyperpop, ILLBEATS, Jazz, K/DA, Maestro, Mixmaster, Mosher, Pentakill, Punk, Rapidfire, Sentinel, Spellweaver, Superfan, TrueDamage, Wildcard
```