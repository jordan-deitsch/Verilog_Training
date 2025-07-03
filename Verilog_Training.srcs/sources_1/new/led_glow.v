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


module led_glow
#(PWM_DUTY_CYCLE = 50)(
    input wire clk_i,
    input wire enable_i,
    output wire led_o
    );
    
    localparam CLK_FREQ_HZ = 12000000;  // 12 MHz clock frequency
    localparam PWM_FREQ_HZ = 10000;     // 10kHz PWM frequency
    localparam PWM_DIVIDE_RATIO = CLK_FREQ_HZ / PWM_FREQ_HZ;
    localparam PWM_DUTY_ON = PWM_DIVIDE_RATIO * PWM_DUTY_CYCLE / 100;
    localparam PWM_COUNTER_WIDTH = $clog2(PWM_DIVIDE_RATIO);

    reg [PWM_COUNTER_WIDTH:0] pwm_counter = 0;
    reg out_buff = 1'b0;
    
    always @(posedge clk_i) begin
        
        if(pwm_counter < PWM_DIVIDE_RATIO) begin
            pwm_counter <= pwm_counter + 1;
        end else begin
            pwm_counter <= 0;
        end
        
        if(pwm_counter < PWM_DUTY_ON) begin
            out_buff <= 1'b1;
        end else begin
            out_buff <= 1'b0;
        end
    end
    
    assign led_o = out_buff;
 
endmodule
