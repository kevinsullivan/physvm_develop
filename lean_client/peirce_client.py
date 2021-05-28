#!/usr/bin/env python
from pathlib import Path

import trio # type: ignore

import random

from trio_server import TrioLeanServer

import time

from datetime import datetime, timedelta

import os

file__ = '/peirce/PeirceOutput.lean'
file_ = '/peirce/PeirceOutput_CHECK.lean'
file_2 = '/peirce/PeirceOutput_CHECK2.lean'

request_file_ = "/peirce/lean_client/boot.touch"
output_file_ = "/peirce/lean_client/output.txt"

#file_ = '/peirce/PeirceOutput.lean'
debug = True

async def update_peirce():
    async with trio.open_nursery() as nursery:
        server = TrioLeanServer(nursery, debug=True)
        await server.start()
        if debug:
            print('BOOT')
            t1=datetime.now()
        await server.full_sync(file__)
        if debug:
            print('END BOOT')
            t2=datetime.now()
            print('BOOT TIME : ')
            print(t2 - t1)
        #f = open("/peirce/lean_client/BOOT.txt", "w")
        #f.write("TOUCH")
       # f.close()
        while True:
            #go_ = 'void'#input()
            #if go_ == 'KILL':
            #    break
            while not os.path.isfile(request_file_):
                time.sleep(.25)
            os.remove(request_file_)

            if debug:
                print ('RUNNING')
                t3 = datetime.now()
            with open(file__) as f:
                content = f.readlines()
            val = random.randint(0, 100000000)
            content = '\n'.join(content) + "\nexample : " + str(val) + "=" + str(val) + ":= rfl"
            await server.full_sync(file__,content)
            if debug:
                print ('RUNNING')
                t4 = datetime.now()
                print(t4 - t3)
            with open(file_) as f:
                content = f.readlines()
            content = '\n'.join(content) + "\nexample : " + str(val) + "=" + str(val) + ":= rfl"
            await server.full_sync(file_,content)
            if debug:
                print('RAN')
                t5=datetime.now()
                print(t5 - t4)
            f = open(output_file_, 'w')
            f.write('\n'.join(server.sync_results))
            f.close()
            #break
        server.kill()
        nursery.cancel_scope.cancel()
if __name__ == '__main__':
    trio.run(update_peirce)
