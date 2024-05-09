import os

folder_to_convert = "../execution-specs/src/ethereum"

# for each file recursively in the folder
for root, dirs, files in os.walk(folder_to_convert):
    for file in files:
        if file.endswith(".py"):
            # convert the file
            full_path = root + "/" + file
            # print("Converting file: " + full_path)
            short_path = full_path[(len(folder_to_convert) + 1):]
            print("Converting file: " + short_path)
            os.system("python main.py " + short_path)
