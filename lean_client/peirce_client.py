#!/usr/bin/env python
from pathlib import Path

from commands import *

import trio # type: ignore

import random

from trio_server import TrioLeanServer

import time

from datetime import datetime, timedelta

import os

peirce_output_ = '/peirce/PeirceOutput.lean'
file_ = '/peirce/PeirceOutput_CHECK.lean'
file_2 = '/peirce/PeirceOutput_CHECK2.lean'

lang_file = '/peirce/lang/lang.lean'
tst_file_ = "/peirce/lean_client/example.lean"

request_file_ = "/peirce/lean_client/boot.touch"
data_file_ = "/peirce/lean_client/boot_data.txt"
output_file_ = "/peirce/lean_client/output.txt"

#file_ = '/peirce/PeirceOutput.lean'
debug = True

async def update_peirce():
    async with trio.open_nursery() as nursery:
        server = TrioLeanServer(nursery, debug=False)
        await server.start()
        if debug:
            print('BOOT')
            t1=datetime.now()

        await server.full_sync(lang_file)
        if debug:
            print('END BOOT')
            t2=datetime.now()
            print('BOOT TIME : ')
            print(t2 - t1)

        while True:
            while not (os.path.isfile(data_file_)):
                time.sleep(.25)
            with open(data_file_,'r') as file:
                dataStr = file.read()
            print("Removing request file")
            from shutil import copyfile
            #copyfile(request_file_ , '/peirce/lean_client/test/boot.touch')
            copyfile(data_file_ , '/peirce/lean_client/test/boot_data.txt')
            #print(os.remove(request_file_))
            print(os.remove(data_file_))
            print(dataStr)
            #server.debug = True
            with open(peirce_output_) as f:
                content = f.read()
            
            val = random.randint(0, 100000000)
            tmpf_ = '/peirce/tmplean'+str(val)+'.lean'
            #print('TMPFNAME')
            #print(tmpf_)
            with open(tmpf_,'w') as f:
                f.write(content + "\nexample : " + str(val) + '=' + str(val) + ":= rfl")
            server.fname = tmpf_
            await server.full_sync(tmpf_)
            sync_results = [s for s in server.sync_results]
            await server.full_sync(tmpf_)
            await server.full_sync(peirce_output_,content)
            sync_results = [s for s in server.sync_results] if len(sync_results) == 0 else sync_results

            os.remove(tmpf_)
            locs = dataStr.split(';')
            ranges = []
            for i in range(len(locs)-1):
                loc = locs[i]
                begend = loc.split(':')
                '''
    begin_line: int
    begin_column: int
    end_line: int
    end_column: int
    error: Optional[str] = None
    type: Optional[str] = None

    Message(file_name='/peirce/PeirceOutput.lean', 
        severity=<Severity.error: 3>, caption='', 
        text='type mismatch at application\n  has_add.add "help"\nterm\n  "help"\nhas type\n  string\nbut is expected to have type\n  
        ℕ', pos_line=16, pos_col=22, end_pos_line=None, end_pos_col=None)

'''
                ranges.append(
                    PeirceRange(
                        int(begend[0].split(',')[0]),
                        int(begend[0].split(',')[1]),
                        int(begend[1].split(',')[0]),
                        int(begend[1].split(',')[1])))
                #print(ranges[-1])
                print('RANGE')
                print(ranges[-1])
                for res in sync_results:
                    #print(res)
                    print('iterating')
                    if 'error' in res.severity and \
                        ((res.pos_line is not None 
                            and (res.pos_line >= ranges[-1].begin_line and res.pos_col >= ranges[-1].begin_column) 
                            and (res.pos_line <= ranges[-1].end_line and res.pos_col <= ranges[-1].end_column)) 
                        or 
                        (res.end_pos_line is not None 
                            and (res.end_pos_line >= ranges[-1].begin_line and res.end_pos_col >= ranges[-1].begin_column) 
                            and (res.end_pos_line <= ranges[-1].end_line and res.end_pos_col <= ranges[-1].end_column))):
                        print('MATCH')
                        ranges[-1].error = res.text
                    else:
                        print(res)
                print('type checking....')
                type_chk_ = await server.state(peirce_output_, ranges[-1].begin_line, ranges[-1].begin_column)
                print(type_chk_)
                print("TYPE???")
                print(type_chk_.state if type_chk_ else None)
                ranges[-1].type = type_chk_.state if type_chk_ else None

      #      if os.path.isfile(request_file_):
      #          print('failed to delete')
      #          raise 'failed to delete'
            if debug:
                print ('RUNNING')
                t3 = datetime.now()

            if debug:
                print ('RUNNING')
                t4 = datetime.now()
                print(t4 - t3)
            
            if debug:
                print('RAN')
                t5=datetime.now()
                print(t5 - t4)
            f = open(output_file_, 'w')
            print('writing...')
            #print(server.sync_results)
            #f.write('\n'.join([str(sr) for sr in sync_results]))
            #f.write('\n')
            f.write('\n'.join([str(r_) for r_ in ranges]))
            f.close()
            copyfile(output_file_ , '/peirce/lean_client/test/output.txt')

        server.kill()
        nursery.cancel_scope.cancel()
if __name__ == '__main__':
    trio.run(update_peirce)
