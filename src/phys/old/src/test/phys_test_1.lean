import ..physlib


/-
worldTime = ClassicalTime()
si = SI()
timeFrame = worldTime.stdFrame() with si
timePoint = Point(worldTime,stdFrame,<10>, si_measurement_system)




timeVector = Vector(worldTime, stdFrame,<60>, si_measurement_system)
newTime = timeFrame(worldTime, timePoint, <timeVector>)
-/

def world_time : _ := _
-- fill in the rest 
-- 