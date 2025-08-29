onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {Synchronous Drives slide}
add wave -noupdate -format Logic -radix decimal /top/cclk
add wave -noupdate -format Literal -radix decimal /top/cout
add wave -noupdate -format Literal -radix decimal /top/p1/c/cout
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
configure wave -namecolwidth 221
configure wave -valuecolwidth 54
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
update
WaveRestoreZoom {0 ns} {99 ns}
