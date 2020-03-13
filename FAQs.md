# Frequently Asked Questions

## Overview
We will update this periodically with relevant questions that come up for developers working on this project.


- How do I add a plug-in to the standard VS Code setup?

In your respective local repository inside your IDE, preferably in a feature branch, go to .vscode -> extensions.json, which has an array called "recommendations". This requires the "id" of the extension, which you should find to the right of the extension name if you search for it in the marketplace. If what I'm saying isn't clear, this provides a clear description as well:  https://code.visualstudio.com/docs/editor/extension-gallery#_recommended-extensions

After that, if you check in the change to extensions.json, other developers just retrieve the change from GitLab. I believe it should ask us to install (although I'm not 100% positive - the documentation seems to suggest that the install prompt may only occur after the first time you load the workspace, but that isn't 100% clear and certainly should be verified).