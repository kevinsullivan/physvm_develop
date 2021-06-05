pkill python3
cd /peirce/Peirce-vscode-api
nohup python3 src/api.py &
cd /peirce/lean_client
nohup python3 /peirce/lean_client/peirce_client.py #not seeming to work with &

#nohup python3 /peirce/lean_client/peirce_client.py &
#cd /peirce/Peirce-vscode-api
#nohup python3 src/api.py &
cd /peirce
