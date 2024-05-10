import os
import subprocess
import sys

folder_to_convert = "../execution-specs/src/ethereum"

# for each file recursively in the folder
for root, dirs, files in os.walk(folder_to_convert):
    for file in files:
        if file.endswith(".py"):
            # convert the file
            full_path = root + "/" + file
            short_path = full_path[(len(folder_to_convert) + 1):]
            print("")
            print("Converting file: " + short_path)

            try:
                command = "python main.py " + folder_to_convert + " " + short_path
                print(command)
                subprocess.run(command, shell=True, check=True)
            except subprocess.CalledProcessError as e:
                print(f"Error occurred: {e}")
                sys.exit(1)
            except KeyboardInterrupt:
                print("Ctrl-C pressed, interrupting the script.")
                sys.exit(1)
