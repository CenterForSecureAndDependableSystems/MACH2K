echo Processing subjects 0-181
for /L %%X in (0,1,9) do (
cd 00%%X
cd trajectory
del 00%%X_mach2k.txt
del mach2ktile.log
call m2k.bat 00%%X
cd ..
cd ..
)
for /L %%X in (10,1,99) do (
cd 0%%X
cd trajectory
del 0%%X_mach2k.txt
del mach2ktile.log
call m2k.bat 0%%X
cd ..
cd ..
)
for /L %%X in (100,1,181) do (
cd %%X
cd trajectory
del %%X_mach2k.txt
del mach2ktile.log
call m2k.bat %%X
cd ..
cd ..
)
echo Complete!