# Assignment #1 

The purpose of this assignment is to get your software environment set up properly participate in this class. 
## Install leanprover-community on your computer(s).

1. If you took my 2102 class in the Fall of 2020, you should be all set, so you're done, so please go to the last task in these instructions to submit your certification that you are all set. Otherwise, please continue.
2. There are three distinct major versions of Lean on the World-Wide Web. (1) Lean version 3, NOT the community version. This was the first Lean Prover public version, developed at Microsoft Research, and is NOT the version you need for this class; (2) Lean version 4 is a brand new version now being developed at Microsoft; it is very interesting but is not ready for prime time and is NOT the version you needed for this class; (3) Lean Version 3 being developed and maintained by the Lean Community. This IS the one you want for this class.
3. The instructions for installing the correct version, along with a great deal of other helpful information, are available [here](https://leanprover-community.github.io/get_started.html). NB: If you're using Windows, we *strongly* recommend that you uninstall whatever previous version of Python you might have already installed. The instructions here assume you don't have Python installed, and if you do have it, you likely have a version that doesn't include the required libraries. So please, if at all possible, please uninstall what you've got, and install the standard version as described in these instructions.

## Get set up to use git, GitHub, and the class git repository

1. If you don't have a GitHub account, please create one for yourself now. You're likely to use this account often in the coming years.
2. Log in to GitHub, visit our [class repository](https://github.com/kevinsullivan/complogic-s21), and *fork* it. This will create a copy of our class repository in your GitHub account.
3. Clone *your* copy of the class repository to your computer(s).

## Get set up to use the VS Code IDE to edit Lean logic/code
1. If you already have VS Code installed, go to the next step, otherwise download and install the current version. It's easily found on the WWW.
2. Run VS Code. Go to the Extensions tab. Search for lean, and install (or be sure you have aleady installed) the lean (jroesch.lean) extension (v.0.16.23 as of 2/10/2021). 

## Make sure everything is working
1. Run VS Code
2. Use *Open Folder* to find the directory into which you cloned your fork of our class repository, and open that *directory*. Don't open the parent directory. Don't open any of the source directories. Open the top-level directory. 
3. Explore some of the code we've written and make sure then when you hover over #eval or #check or #reduce commands, that Lean is giving you appropriate feedback.

## Submit your work

To complete this assignment, go to Collab, select Assignment #1 under Assignments, and just submit the simple line of text certifying that you've completed the assignment, e.g., "I'm done and it works. Yay!"