`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/03/2025 02:19:14 PM
// Design Name: 
// Module Name: led_glow
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


module led_glow(
    input wire clk_i,
    output wire led_o
    );

    reg [23:0] cnt;
    reg [4:0] PWM;
    wire [3:0] intensity = cnt[23] ? cnt[22:19] : ~cnt[22:19];
    
    always @(posedge clk_i) begin
        cnt <= cnt+1;
        PWM <= PWM[3:0] + intensity;
    end
    
    assign led_o = PWM[4];
 
endmodule
