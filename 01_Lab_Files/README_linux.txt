************************************************************
*****                                                  *****
*****           SystemVerilog for Verification         *****
*****                                                  *****
*****                     Hardent                      *****
*****                                                  *****
************************************************************

#### To prepare the labs for a class:

 1. tar -zxvf <path to file_name.tgz>
 (or first gunzip <path to file_name.tgz>
 then tar -xvf <path to file_name.tar> if -z option unsupported)

#### Database checkout

   $ cd database_test

------For Questasim:
   $ make

------For VCS
   $ make vcs

------For Incisive
   $ make irun

------For Xceilium
   $ make xrun

The output should end with following. Note however, different versions
of the simulator and different simulators
may end up with a different number of Matches or a different number of
transactions to meet 100% coverage because of randomization - that is OK
There should be no mismatches and 100% coverage:

        Router size = 8x8
        stim_gen:  Creating 1000 Packets


        ********************************
        Matches:    994
        Mismatches: 0
        Missing:    1

        ********************************


        ********************************
         Final Coverage = 100.000000%
         100% Coverage met with 380 transactions
        ********************************

