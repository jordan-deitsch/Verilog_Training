# WHDL SystemVerilog for Verification Course
#  - Setup & simulation script for

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
vlog  sva_ex.sv
vsim -voptargs=+acc -assertdebug sva_ex

# run simulation
#run -all
