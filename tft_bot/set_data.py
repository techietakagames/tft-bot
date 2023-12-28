class Set10:
    trait_cutoffs = {
        "8-bit": [2, 4, 6],
        "Country": [3, 5, 7],
        "Disco": [3, 4, 5, 6],
        "EDM": [2, 3, 4, 5],
        "Emo": [2, 4, 6],
        "Heartsteel": [3, 5, 7, 10],
        "Hyperpop": [1, 2, 3, 4],
        "ILLBEATS": [1],
        "Jazz": [2, 3, 4],
        "K/DA": [3, 5, 7, 10],
        "Maestro": [1],
        "Mixmaster": [1],
        "Pentakill": [3, 5, 7, 10],
        "Punk": [2, 4, 6],
        "TrueDamage": [2, 4, 6, 9],
        "Wildcard": [1],
        "BigShot": [2, 4, 6],
        "Breakout": [1],
        "Bruiser": [2, 4, 6],
        "CrowdDiver": [2, 4, 6],
        "Dazzler": [2, 4, 6],
        "Edgelord": [3, 5, 7],
        "Executioner": [2, 4, 6],
        "Guardian": [2, 4, 6],
        "Mosher": [2, 4, 6],
        "Rapidfire": [2, 4, 6],
        "Sentinel": [2, 4, 6, 8],
        "Spellweaver": [3, 5, 7, 10],
        "Superfan": [3, 4, 5],
    }

    champ_traits = {
        'Ahri': ['K/DA', 'Spellweaver'],
        'Akali-TD': ['TrueDamage', 'Breakout', 'Executioner'],
        'Akali-KDA': ['K/DA', 'Breakout', 'Executioner'],
        'Amumu': ['Emo', 'Guardian'],
        'Annie': ['Emo', 'Spellweaver'],
        'Aphelios': ['Heartsteel', 'Rapidfire'],
        'Bard': ['Jazz', 'Dazzler'],
        'Blitzcrank': ['Disco', 'Sentinel'],
        'Caitlyn': ['8-bit', 'Rapidfire'],
        'Corki': ['8-bit', 'BigShot'],
        'Ekko': ['TrueDamage', 'Sentinel', 'Spellweaver'],
        'Evelynn': ['K/DA', 'CrowdDiver'],
        'Ezreal': ['Heartsteel', 'BigShot'],
        'Garen': ['8-bit', 'Sentinel'],
        'Gnar': ['Pentakill', 'Mosher', 'Superfan'],
        'Gragas': ['Disco', 'Bruiser', 'Spellweaver'],
        'Illaoi': ['ILLBEATS', 'Bruiser'],
        'Jax': ['EDM', 'Mosher'],
        'Jhin': ['Maestro', 'BigShot'],
        'Jinx': ['Punk', 'Rapidfire'],
        'KSante': ['Heartsteel', 'Sentinel'],
        'KaiSa': ['K/DA', 'BigShot'],
        'Karthus': ['Pentakill', 'Executioner'],
        'Katarina': ['Country', 'CrowdDiver'],
        'Kayle': ['Pentakill', 'Edgelord'],
        'Kayn': ['Heartsteel', 'Wildcard', 'Edgelord'],
        'Kennen': ['TrueDamage', 'Guardian', 'Superfan'],
        'Lillia': ['K/DA', 'Sentinel', 'Superfan'],
        'Lucian': ['Jazz', 'Rapidfire'],
        'Lulu': ['Hyperpop', 'Spellweaver'],
        'Lux': ['EDM', 'Dazzler'],
        'MissFortune': ['Jazz', 'BigShot'],
        'Mordekaiser': ['Pentakill', 'Sentinel'],
        'Nami': ['Disco', 'Dazzler'],
        'Neeko': ['K/DA', 'Guardian', 'Superfan'],
        'Olaf': ['Pentakill', 'Bruiser'],
        'Pantheon': ['Punk', 'Guardian'],
        'Poppy': ['Emo', 'Mosher'],
        'Qiyana': ['TrueDamage', 'CrowdDiver'],
        'Riven': ['8-bit', 'Edgelord'],
        'Samira': ['Country', 'Executioner'],
        'Senna': ['TrueDamage', 'Rapidfire'],
        'Seraphine': ['K/DA', 'Spellweaver'],
        'Sett': ['Heartsteel', 'Bruiser', 'Mosher'],
        'Sona': ['Mixmaster', 'Spellweaver'],
        'TahmKench': ['Country', 'Bruiser'],
        'Taric': ['Disco', 'Guardian'],
        'Thresh': ['Country', 'Guardian'],
        'Twisted': ['Disco', 'Dazzler'],
        'Twitch': ['Punk', 'Executioner'],
        'Urgot': ['Country', 'Mosher'],
        'Vex': ['Emo', 'Executioner'],
        'Vi': ['Punk', 'Mosher'],
        'Viego': ['Pentakill', 'Edgelord'],
        'Yasuo': ['TrueDamage', 'Edgelord'],
        'Yone': ['Heartsteel', 'CrowdDiver', 'Edgelord'],
        'Yorick': ['Pentakill', 'Guardian', 'Mosher'],
        'Zac': ['EDM', 'Bruiser'],
        'Zed': ['EDM', 'CrowdDiver'],
        'Ziggs': ['Hyperpop', 'Dazzler'],
    }

    spatula_traits = ["8-bit", "Emo", "Heartsteel", "Jazz", "K/DA", "Pentakill", "Punk", "TrueDamage"]


    trait_champs = {}
    champs = []
    traits = []
    def __init__(self):
        for champ, traits in Set10.champ_traits.items():
            for trait in traits:
                arr = Set10.trait_champs.get(trait, [])
                arr.append(champ)
                Set10.trait_champs[trait] = arr
        Set10.champs = sorted(list(Set10.champ_traits.keys()))
        Set10.traits = sorted(list(Set10.trait_cutoffs.keys()))
    @staticmethod
    def get_non_unique_traits():
        non_unique_traits = []
        for trait, cutoffs in Set10.trait_cutoffs.items():
            if len(cutoffs) > 1 or cutoffs[0] != 1:
                non_unique_traits.append(trait)
        return non_unique_traits


