# How to run Peirce
There are multiple ways to run Peirce. The following steps should be taken regardless of the method you're running:
1. Complete the Onboarding tutorial, found in ONBOARD.md
2. Make sure your Docker instance is running, and that VS Code is connected to the docker container

From here, there are 3 ways to run Peirce. Through VSCode, directly over the terminal, or via the VScode plugin.

# Through VSCode

3. Open up a terminal window on your native machine
4. Type in "docker exec -it peirce_docker /bin/bash" so that you have a shell inside the docker container.
5. Type "sh /peirce/run_lean_client.sh". Wait ~2 minutes for the Lean Server to boot.
6. Go to your .vscode folder and click launch.json
7. You will see a line that says: "args": ["CONFIGURABLE_FILENAME", "-extra-arg=-I/opt/ros/melodic/include/"]. Replace "CONFIGURABLE_FILENAME" with the ROS test program you would like to run Peirce on.
8. Hit F5, which will launch Peirce using a text-based UI in the VSCode terminal window
   
# Over the Command Line

3. Open up a terminal window on your native machine
4. Type in "docker exec -it peirce_docker /bin/bash" so that you have a shell inside the docker container.
5. Type "source /peirce/run_lean_client.sh". Wait ~2 minutes for the Lean Server to boot.
6. In your main VSCode terminal window, type /peirce/bin/peirce FILE_NAME -extra-arg=-I/opt/ros/melodic/include/
7. Replace "FILE_NAME" with the ROS C++ file that you wish to run Peirce over.
8. (OPTIONAL) When running Peirce, you'll notice that a file is created at /peirce/annotations.txt, which contains a "log" of all the commands you entered. This file can be used to construct unit tests or to "replay" runs of Peirce. To use this file, simply run the command from step 6 with a small addendum: /peirce/bin/peirce FILE_NAME -extra-arg=-I/opt/ros/melodic/include/ < /peirce/annotations.txt
9. This annotations.txt file can be moved and renamed into a unit test folder to capture runs of Peirce on different files.

# Using the VSCode Plugin

3. Open up 2 terminal windows on your native machine
4. Type in "docker exec -it peirce_docker /bin/bash" on both terminals so that you have a shell inside the docker container.
5. Next, type in source 
6. In the first terminal, type "source /peirce/run_api.sh"
7. In the second terminal, type "source /peirce/run_lean_client.sh" (and wait 2 minutes for the server to boot)
8. Go back to the terminal in your VSCode. Type in "source /peirce/install_plugin.sh". You should see that an additional button on the left-hand VSCode menu has just been added
9. Next, navigate to the C++ file that you wish to annotate, click inside it, and open up the plugin tab on the left hand menu. Typing in CTRL+ALT+R will populate the Table of Terms from Peirce.