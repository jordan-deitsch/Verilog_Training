`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/09/2025 12:12:40 PM
// Design Name: 
// Module Name: iic_monitor
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


module iic_monitor(
    input wire clk_i,
    input wire reset_i,
    input wire i2c_scl_i,
    input wire i2c_sda_i
    );
    
    // IIC States
    localparam IIC_BUS_IDLE         = 4'h0;
    localparam IIC_START_CONDITION  = 4'h1;
    localparam IIC_START_RECEIVED   = 4'h2;
    localparam IIC_SENDING_ADDRESS  = 4'h3;
    localparam IIC_SENDING_DATA     = 4'h4;
    localparam IIC_WAITING_FOR_ACK  = 4'h5;
    localparam IIC_ERROR            = 4'hF;
    
    // Edge definitions
    localparam RISING_EDGE          = 2'b01;
    localparam FALLING_EDGE         = 2'b10;
    localparam IDLE_MODE            = 2'b11;
    
    // IIC Timing Requirements as integer clk_i clock cycles 
    // Clock period = 10 nsec
    reg [31:0] T_BUFF               = 32'd60;   // 600 nsec
    reg [31:0] T_HDSTA              = 32'd10;   // 100 nsec
    reg [31:0] T_SUSTA              = 32'd10;   // 100 nsec
    reg [31:0] T_SUSTO              = 32'd10;   // 100 nsec
    reg [31:0] T_HDDAT_MIN          = 32'd01;   // 10 nsec
    reg [31:0] T_HDDAT_MAX          = 32'd90;   // 900 nsec
    reg [31:0] T_SUDAT              = 32'd10;   // 100 nsec
    reg [31:0] T_LOW                = 32'd130;  // 1300 nsec
    reg [31:0] T_HIGH               = 32'd60;   // 600 nsec
    
    // Track minimum delay times of IIC protocol and signal edges
    reg [31:0] scl_delay_counter    = 32'h0;
    reg [31:0] sda_delay_counter    = 32'h0;
    reg [1:0] scl_buff              = IDLE_MODE;
    reg [1:0] sda_buff              = IDLE_MODE;
    
    // Output variables from state machine
    reg [31:0] scl_delay_val        = 32'h0;
    reg [31:0] sda_delay_val        = 32'h0;
    reg [7:0] device_address        = 8'h0;
    reg [7:0] data_byte             = 8'h0;
    reg [3:0] bit_counter           = 4'h0;
    reg [31:0] error_code           = 32'h0;
    
    // State machine variables, initialized to IIC_IDLE state
    reg [3:0] current_state         = IIC_BUS_IDLE;
    reg [3:0] next_state            = IIC_BUS_IDLE;
    
    // Update state
    always @(posedge clk_i) begin
        if(reset_i == 1'b0) begin
            current_state <= IIC_BUS_IDLE;
            scl_delay_counter <= 32'h0;
            sda_delay_counter <= 32'h0;
            scl_buff <= IDLE_MODE;
            sda_buff <= IDLE_MODE;
        end
        else begin
            // Update signal buffers for edge detection
            scl_buff <= { scl_buff[0], i2c_scl_i };
            sda_buff <= { sda_buff[0], i2c_sda_i };
            
            // Check if minimum delays are valid before transitioning to next state
            if((scl_delay_counter == 0) && (scl_delay_counter == 0)) begin
                current_state <= next_state;
            end else begin
                // Update error code
            end
            
            // Decrement delay counters to 0, or reset when transitioning state
            if(next_state != current_state) begin
                scl_delay_counter <= scl_delay_val;
                sda_delay_counter <= sda_delay_val;
            end else begin
                if(scl_delay_counter) scl_delay_counter <= scl_delay_counter - 1;
                if(sda_delay_counter) sda_delay_counter <= sda_delay_counter - 1;
            end
        end
    end
    
    // Change state logic
    always @(current_state, i2c_scl_i, i2c_sda_i) begin
    case(current_state)
    
    IIC_BUS_IDLE: 
    begin
        if(i2c_scl_i == 1'b1 && i2c_sda_i == 1'b0) begin
            next_state <= IIC_START_CONDITION;
        end else begin
            next_state <= current_state;
        end
        
        device_address <= 8'h0;
        data_byte <= 8'h0;
        bit_counter <= 4'h0;

    end
    
    IIC_START_CONDITION: 
    begin
        if(i2c_scl_i == 1'b0 && i2c_sda_i == 1'b0) begin
            next_state <= IIC_SENDING_ADDRESS;
        end else if(i2c_scl_i == 1'b1 && i2c_sda_i == 1'b1) begin
            next_state <= IIC_ERROR;
        end else begin
            next_state <= current_state;
        end 
    end
    
    IIC_SENDING_ADDRESS:
    begin
        if(scl_buff == RISING_EDGE) begin
            bit_counter <= bit_counter + 1;
        end
        if (bit_counter == 4'd9) begin
        end
    end
    
    
    
    default begin
        next_state <= IIC_ERROR;
    end
    
    endcase
    
    end
    
    
endmodule
