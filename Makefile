SHELL=bash

# check that script files are accepted by hol 
all:
	Holmake fs_specTheory.uo dir_treeTheory.uo sslTheory.uo spec_with_sslTheory.uo

#	cat fs_specScript.sml dir_treeScript.sml |hol

clean:
	Holmake cleanAll
