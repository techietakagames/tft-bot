# XXX does not work on akali
def scrape_champs_to_traits():
    champs_traits = {}
    with open("../data/champ_list.txt") as stream:
        start_champ = True
        curr_traits = []
        for line in stream:
            line = line.strip()
            arr = line.split()
            if start_champ:
                name = arr[0]
                start_champ = False
            else:
                try:
                    int(arr[0])
                    start_champ = True
                    champs_traits[name] = curr_traits
                    curr_traits = []
                    continue
                except:
                    pass
            if arr[0] != name:
                if arr[0] == "Crowd":
                    curr_traits.append("CrowdDiver")
                elif arr[0] == "Big":
                    curr_traits.append("BigShot")
                elif arr[0] == "True":
                    curr_traits.append("TrueDamage")
                else:
                    curr_traits.append(arr[0])

    for i,j in champs_traits.items():
        print("'" + i + "': " + str(j) + ",")

if __name__ == '__main__':
    scrape_champs_to_traits()