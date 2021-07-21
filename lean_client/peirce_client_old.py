#!/usr/bin/env python
from pathlib import Path

from commands import *

import trio # type: ignore

import random

from trio_server import TrioLeanServer

import time

from datetime import datetime, timedelta

import os

file__ = '/peirce/PeirceOutput.lean'
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
        server = TrioLeanServer(nursery, debug=True)
        await server.start()
        if debug:
            print('BOOT')
            t1=datetime.now()

        tst_file_ = '/peirce/PeirceOutput.lean'
        #ah = await server.roi(tst_file_, 14, 15)
        #print(ah)
        with open(tst_file_) as f:
            content = f.read()

        content = '''import .lang.expressions.time_expr
import .lang.expressions.geom1d_expr

import .lang.expressions.geom3d_expr

open lang.time
open lang.geom1d
open lang.geom3d
namespace peirce_output
def pttt : nat := 1

def pf1c : _ := 1
def pf2c : _ := (1:nat)
def pf3c : _ := ((1:nat):_)
def World_fr : time_frame_expr := |time_std_frame|
def World : time_space_expr World_fr := |time_std_space|


def pttt : ℕ := "help"+y
def t1 : duration_expr (|time_std_space| : time_space_expr (|time_std_frame|)) := | mk_duration _ 1|
def c1 : _ := ((|mk_duration World.value 1|:_)+(|mk_duration World.value 1|:_))
def c2 : _ := |mk_duration World.value 1|
def c3 : _ := (|mk_duration World.value 1|:_)
def c4 : _ := (|mk_duration World.value 1|+ᵥ(|mk_time World.value 1|:_):_)
def c5 : _ := ((|mk_duration World.value 1|:_)+ᵥ|mk_time World.value 1|:_)
def c6 : _ := (t1.value+ᵥt1.value:_)
--def c6 : duration_expr World := (_)


--def cartesian_world_transform_0 : _ := ((transform_world_pose_.value : _)∘((cartesian_pose_with_orientation)⁻¹).value : _)


/-

def World_fr : geom3d_frame_expr := |geom3d_std_frame|
def World : geom3d_space_expr World_fr := |geom3d_std_space|
-/

end peirce_output'''

        #await server.full_sync(lang_file)
        
        await server.full_sync(tst_file_)#, content)

        
        for i in range(17,20):
            print('AT I' + str(i))
            val_ = await server.state(tst_file_, 13, i)
            val_ = await server.state(tst_file_, 14, i)
        for i in range(17,20):
            print('AT I' + str(i))
            val_ = await server.state(tst_file_, 13, i)
            val_ = await server.state(tst_file_, 14, i)
        
        
        with open(tst_file_) as f:
            content = f.readlines()
            val = random.randint(0, 100000000)
            content = '\n'.join(content) + "\nexample : " + str(val) + "=" + str(val) + ":= rfl"
        
        content = '''import .lang.expressions.time_expr
import .lang.expressions.geom1d_expr

import .lang.expressions.geom3d_expr

open lang.time
open lang.geom1d
open lang.geom3d
namespace peirce_output
def pttt : nat := 1

def pf1c : _ := 1
def pf2c : _ := 5+5
def pf3c : _ := (6+(12+12))
def World_fr : time_frame_expr := |time_std_frame|
def World : time_space_expr World_fr := |time_std_space|


def pttt : ℕ := "help"+y
def t1 : duration_expr (|time_std_space| : time_space_expr (|time_std_frame|)) := | mk_duration _ 1|
def c1 : _ := ((|mk_duration World.value 1|:_)+(|mk_duration World.value 1|:_))
def c2 : _ := |mk_duration World.value 1|
def c3 : _ := (|mk_duration World.value 1|:_)
def c4 : _ := (|mk_duration World.value 1|+ᵥ(|mk_time World.value 1|:_):_)
def c5 : _ := ((|mk_duration World.value 1|:_)+ᵥ|mk_time World.value 1|:_)
def c6 : _ := (t1.value+ᵥt1.value:_)
--def c6 : duration_expr World := (_)


--def cartesian_world_transform_0 : _ := ((transform_world_pose_.value : _)∘((cartesian_pose_with_orientation)⁻¹).value : _)


/-

def World_fr : geom3d_frame_expr := |geom3d_std_frame|
def World : geom3d_space_expr World_fr := |geom3d_std_space|
-/

end peirce_output'''
        #await server.full_sync(tst_file_, "")
        with open(tst_file_) as f:
            content = f.read()
            val = random.randint(0, 100000000)
            #content = '\n'.join(content) + "\nexample : " + str(val) + "=" + str(val) + ":= rfl"

        #tst_file_ = '/peirce/whatnow.lean'
        #with open(tst_file_, 'w') as f:
        #    f.write("")
        #await server.full_sync(tst_file_)
        #await server.full_sync(tst_file_)
        with open('/peirce/whatnow.lean', 'w') as f:
            f.write(content)
        await server.full_sync('/peirce/whatnow.lean')

        
        for i in range(17,20):
            print('AT I' + str(i))
            val_ = await server.state(tst_file_, 13, i)
            val_ = await server.state(tst_file_, 14, i)

        #os.remove(tst_file_)
        raise 'brk'
        #time.sleep(5)
        #for i in range(10):
        #    val_ = await server.state(tst_file_, 10, 2*i)
        #    val_ = await server.state(tst_file_, 11, 10*i)
        #    val_ = await server.state(tst_file_, 14, 12*i)
        #for i in range(111):
        #    val_ = await server.state(tst_file_, 14, i)
        for i in range(14,18):
            print('AT I' + str(i))
            val_ = await server.state(tst_file_, 22, i)
            val_ = await server.state(tst_file_, 23, i)

        #raise "shut off"


        for i in range(14,22):
            print('I::'+str(i))
            print('I::'+str(i))
            print('I::'+str(i))
            print('I::'+str(i))
            print('I::'+str(i))
            print('I::'+str(i))
            print('I::'+str(i))
            print('I::'+str(i))
            print('I::'+str(i))
            print('AAAAA')
            print('AAAAA')
            print('AAAAA')
            print('AAAAA')
            print('AAAAA')
            print('AAAAA')
            val_ = await server.state(tst_file_, 21, i)
            #val_ = await server.complete(tst_file_, 21, i)
            print('BBBBB')
            print('BBBBB')
            print('BBBBB')
            print('BBBBB')
            print('BBBBB')
            print('BBBBB')
            val_ = await server.state(tst_file_, 24, i)
            #val_ = await server.complete(tst_file_, 24, i)
            print('CCCCC')
            print('CCCCC')
            print('CCCCC')
            print('CCCCC')
            print('CCCCC')
            print('CCCCC')
            val_ = await server.state(tst_file_, 25, i)
            #val_ = await server.complete(tst_file_, 25, i)

        raise "shut off"

        ah = await server.all_holes(tst_file_)
        #for i in range(10,101):
        #    print('I::'+str(i))
        #    val_ = await server.state(tst_file_, 14, i)
        #    if i < 40:
        #        val_ = await server.complete(tst_file_, 14, i)
        ah = await server.all_holes(tst_file_)
        for r_ in ah.holes:
            print(r_)
            for h_ in r_.results:
                print(h_)
            inf_ = await server.inf_hole(tst_file_, r_.start.line, r_.start.column)
        #ah = await server.roi(tst_file_, 14, 15)
        #print(ah)
        #for i in range(95):
        #    val_ = await server.state(tst_file_, 12, i)

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

            while not (os.path.isfile(request_file_) or os.path.isfile(data_file_)):
                time.sleep(.25)
            print("Removing request file")
            print(os.remove(request_file_))
            with open(data_file_,'r') as file:
                dataStr = file.read()
            print(dataStr)

            locs = dataStr.split(';')
            ranges = []
            for i in range(len(locs)-1):
                loc = locs[i]
                begend = loc.split(':')
                ranges.append(PeirceRange(begend[0].split(',')[0],begend[0].split(',')[1],begend[1].split(',')[0],begend[1].split(',')[1]))
            print(ranges)
            print(os.remove(data_file_))

            if os.path.isfile(request_file_):
                print('failed to delete')
                raise 'failed to delete'
            if debug:
                print ('RUNNING')
                t3 = datetime.now()
            with open(file__) as f:
                content = f.readlines()
            val = random.randint(0, 100000000)
            content = '\n'.join(content) + "\nexample : " + str(val) + "=" + str(val) + ":= rfl"

            #for loc in ranges[1:2]:
            #    tst1 = await server.state(file__, loc.begin_line, loc.begin_column)
            #    tst2 = await server.state(file__, loc.begin_line, int(loc.begin_column)+int(1))
            #    tst3 = await server.state(file__, loc.end_line, loc.end_column)
            #    print('1:'+tst1)
            #    print('2:'+tst2)
            #    print('3:'+tst3)

            print('NEXT')

            await server.full_sync(file__)#,content)
            
            #for loc in ranges[1:2]:
            #    tst1 = await server.state(file__, loc.begin_line, loc.begin_column)
            #    tst2 = await server.state(file__, loc.begin_line, int(loc.begin_column)+int(1))
            #    tst3 = await server.state(file__, loc.end_line, loc.end_column)
            #    print('1:'+tst1)
            #    print('2:'+tst2)
            #    print('3:'+tst3)
            #for i in range(1,111):
            #    tst1 = await server.state(file__, 14, i)
            #    print(tst1)

            if debug:
                print ('RUNNING')
                t4 = datetime.now()
                print(t4 - t3)
            with open(file_) as f:
                content = f.readlines()
            content = '\n'.join(content) + "\nexample : " + str(val) + "=" + str(val) + ":= rfl"
            await server.full_sync(file_)#,content)
            for i in range(20):
                print('NEXT')
                
            #print('SHOULD WRITE?')
            #print(server.sync_results)

            #await server.full_sync(file__)
            #await server.full_sync(file__)
            #for loc in ranges[1:2]:
            #    tst1 = await server.state(file__, loc.begin_line, loc.begin_column)
            #    tst2 = await server.state(file__, loc.begin_line, int(loc.begin_column)+int(1))
            #    tst3 = await server.state(file__, loc.end_line, loc.end_column)
            #    print('1:'+tst1)
            #    print('2:'+tst2)
            #    print('3:'+tst3)
            
            if debug:
                print('RAN')
                t5=datetime.now()
                print(t5 - t4)
            f = open(output_file_, 'w')
            print('writing...')
            print(server.sync_results)
            f.write('\n'.join(server.sync_results))
            f.close()
            #break
        server.kill()
        nursery.cancel_scope.cancel()
if __name__ == '__main__':
    trio.run(update_peirce)
