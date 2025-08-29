atv log -asserts -enable /sva_ex/assert_count3
add wave /sva_ex/assert_count3
run -all
add atv /sva_ex/assert_count3 20ns
