nvm install node
nvm use node
cd /peirce/Peirce-vscode
npm install
npm install -g vsce
vsce package
code --install-extension /peirce/Peirce-vscode/code-annotation-0.0.1.vsix

cd /peirce

#nohup python3 src/api.py &