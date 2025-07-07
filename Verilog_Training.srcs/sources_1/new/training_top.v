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
    input wire clk_i,
    input wire [3:0] button_i,
    input wire [3:0] switch_i,
    output wire [3:0] led_o
    );
    
    led_blinker blinker_mod(
        .clk_i      ( clk_i         ),
        .rst_i      ( button_i[0]   ),
        .enable_i   ( switch_i[0]   ),
        .led_o      ( led_o[0]      )
    );
    
    led_glow glow_mod(
        .clk_i      ( clk_i         ),
        .led_o      ( led_o[1]      )
    );
    
    pwm_generator pwm_mod(
        .clk_i      ( clk_i         ),
        .enable_i   ( switch_i[1]   ),
        .pwm_o      ( led_o[2]      )
    );
    
    assign led_o[3] = 1'b0;
    
endmodule
