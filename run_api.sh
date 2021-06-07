pkill python3
cd /peirce/Peirce-vscode-api
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt

#nohup python3 src/api.py &
python3 src/api.py


#cd /peirce