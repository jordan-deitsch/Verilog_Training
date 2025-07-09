`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2025 02:26:55 PM
// Design Name: 
// Module Name: training_top
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module training_top(
    input wire sys_clk,
    input wire reset,
    input wire [3:0] button_i,
    input wire [3:0] switch_i,
    output wire [3:0] led_o,
    
    inout wire i2c_scl_io,
    inout wire i2c_sda_io
    );
    
    led_blinker blinker_mod(
        .clk_i      ( sys_clk       ),
        .rst_i      ( button_i[0]   ),
        .enable_i   ( switch_i[0]   ),
        .led_o      ( led_o[0]      )
    );
    
    led_glow glow_mod(
        .clk_i      ( sys_clk       ),
        .led_o      ( led_o[1]      )
    );
    
    pwm_generator pwm_mod(
        .clk_i      ( sys_clk       ),
        .enable_i   ( switch_i[1]   ),
        .pwm_o      ( led_o[2]      )
    );
    
    assign led_o[3] = 1'b0;

    wire i2c_scl_i;
    wire i2c_scl_o;
    wire i2c_scl_t;
    wire i2c_sda_i;
    wire i2c_sda_o;
    wire i2c_sda_t;

    IOBUF i2c_scl_iobuf(
        .I(i2c_scl_o),
        .IO(i2c_scl_io),
        .O(i2c_scl_i),
        .T(i2c_scl_t)
    );
        
    IOBUF i2c_sda_iobuf(
        .I(i2c_sda_o),
        .IO(i2c_sda_io),
        .O(i2c_sda_i),
        .T(i2c_sda_t)
    );
        
    training_bd training_bd_i(
        .reset      (reset),
        .sys_clk_in (sys_clk),
        .i2c_scl_i  (i2c_scl_i),
        .i2c_scl_o  (i2c_scl_o),
        .i2c_scl_t  (i2c_scl_t),
        .i2c_sda_i  (i2c_sda_i),
        .i2c_sda_o  (i2c_sda_o),
        .i2c_sda_t  (i2c_sda_t),
        
        .i2c_mon_scl_i (i2c_sda_i),
        .i2c_mon_sda_i (i2c_sda_i)
    );
    
endmodule
