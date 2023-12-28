
import tft_bot.main as t

def test_basic():
    t.main("")

def test_more_champs():
    arr = "--num-champs 4".split()
    t.main(arr)

def test_multi_talented():
    arr = "--multi-talented".split()
    t.main(arr)

def test_max_traits_many_champs():
    arr = "--num-champs 10".split()
    t.main(arr)

def test_max_non_unique_traits_many_champs():
    arr = "--num-champs 10 -m max-non-unique-traits".split()
    t.main(arr)

def test_max_non_unique_traits_many_champs_multi_talent():
    arr = "--num-champs 10 -m max-non-unique-traits -t".split()
    t.main(arr)

def test_max_non_unique_traits_many_champs_multi_talent_and_two_spatulas():
    arr = "--num-champs 10 -p -m max-non-unique-traits -s 2".split()
    t.main(arr)

def test_max_non_unique_traits_many_champs_multi_talent_and_two_spatulas_and_bard_jhin_qiyana():
    arr = "--num-champs 10 -p -m max-non-unique-traits -s 2 -c Bard Jhin Qiyana".split()
    t.main(arr)

def test_max_non_unique_traits_many_champs_multi_talent_and_two_spatulas_and_jazz_4():
    arr = "--num-champs 10 -p -m max-non-unique-traits -s 2 -t Jazz 4".split()
    t.main(arr)
def test_max_non_unique_traits_many_champs_multi_talent_and_two_spatulas_and_bard_jhin_qiyana_and_jazz_4():
    arr = "--num-champs 10 -p -m max-non-unique-traits -s 2 -c Bard Jhin Qiyana -t Jazz 4".split()
    t.main(arr)

def test_max_non_unique_traits_many_champs_multi_talent_and_two_spatulas_and_not_bard_miss_fortune_and_jazz_4():
    arr = "--num-champs 10 -p -m max-non-unique-traits -s 2 -b Bard MissFortune -t Jazz 4".split()
    t.main(arr)


"""
def test_list_champs():
    arr = "--list-champs".split()
    t.main(arr)

def test_list_traits():
    arr = "--list-traits".split()
    t.main(arr)
"""