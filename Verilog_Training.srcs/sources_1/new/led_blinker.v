`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/02/2025 01:30:31 PM
// Design Name: 
// Module Name: led_blinker
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


module led_blinker(
    input clk_i,
    input rst_i,
    input enable_i,
    output [3:0] led_o
    );
    
    localparam CLK_FREQ_HZ = 12000000;
    localparam CLK_DIVIDE = 6000000;
    localparam COUNTER_WIDTH = $clog2(CLK_DIVIDE);
    
    reg [3:0] led_buff = 4'h0;
    reg [COUNTER_WIDTH-1:0] counter = 32'h0;
    
    assign led_o = led_buff;
    
    always @(posedge clk_i) begin
        if(rst_i == 1'b1) begin
            led_buff <= 4'b0;
            counter <= 32'h0;
        end else begin
            if(enable_i == 1'b1) begin
                if(counter == CLK_DIVIDE) begin
                    led_buff <= ~led_buff;
                    counter <= 32'h0;
                end else begin
                    counter <= counter + 1;
                end
            end
        end
    end
    
endmodule
