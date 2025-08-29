# WHDL SystemVerilog for Verification Course
#  - Setup & simulation script for
#  SVA UART Lab

onbreak {resume}
onerror {quit -f}

if [file exists work] {
    vdel -all
}
vlib work

echo "#"
echo "# NOTE: Starting simulator and running DEMO ..."
echo "#"

# compile & run first simulation
vlog   ./test_u_xmit.sv ./u_xmit.sv +define+BAD=1 +acc=a
vsim -voptargs=+acc -assertdebug test_u_xmit

# run simulation
#run -all

