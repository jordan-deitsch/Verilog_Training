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


module iic_monitor
#(  parameter T_BUF       = 32'd60,   // 600 nsec
    parameter T_HDSTA     = 32'd10,   // 100 nsec
    parameter T_SUSTA     = 32'd10,   // 100 nsec
    parameter T_SUSTO     = 32'd10,   // 100 nsec
    parameter T_HDDAT_MIN = 32'd01,   // 10 nsec
    parameter T_HDDAT_MAX = 32'd90,   // 900 nsec
    parameter T_SUDAT     = 32'd10,   // 100 nsec
    parameter T_LOW       = 32'd130,  // 1300 nsec
    parameter T_HIGH      = 32'd60)   // 600 nsec
(
    input wire clk_i,
    input wire reset_i,
    input wire i2c_scl_i,
    input wire i2c_sda_i,
    
    output wire         ack_o,
    output wire [7:0]   address_o,
    output wire [7:0]   data_o,
    output wire [3:0]   state_o,
    output wire [31:0]  error_o
);
    
    // IIC States
    localparam STATE_RESET      = 4'h0;
    localparam STATE_IDLE       = 4'h1;
    localparam STATE_START      = 4'h2;
    localparam STATE_BYTE_START = 4'h3;
    localparam STATE_HIGH_DATA  = 4'h4;
    localparam STATE_LOW_DATA   = 4'h5;
    localparam STATE_BYTE_END   = 4'h6;
    localparam STATE_ERROR      = 4'hF;
    
    // Edge definitions
    localparam RISING_EDGE      = 2'b01;
    localparam FALLING_EDGE     = 2'b10;
    localparam IIC_IDLE         = 2'b11;
    localparam IIC_BITS_PER_WORD = 8;       // 8 data bits, does not include ACK/NACK bit
    
    // Error Codes for timing violations
    localparam T_BUF_ERROR_CODE         = 1 << 0;
    localparam T_HDSTA_ERROR_CODE       = 1 << 1;
    localparam T_SUSTA_ERROR_CODE       = 1 << 2;
    localparam T_SUSTO_ERROR_CODE       = 1 << 3;
    localparam T_HDDAT_MIN_ERROR_CODE   = 1 << 4;
    localparam T_HDDAT_MAX_ERROR_CODE   = 1 << 5;
    localparam T_SUDAT_ERROR_CODE       = 1 << 6;
    localparam T_LOW_ERROR_CODE         = 1 << 7;
    localparam T_HIGH_ERROR_CODE        = 1 << 8;
    localparam SDA_TRANS_ERROR_CODE     = 1 << 9;
    
    // IIC Timing Requirements as integer clk_i clock cycles 
    // Clock period = 10 nsec

    
    // Track minimum delay times of IIC protocol and signal edges
    reg [31:0] scl_delay_counter        = 32'h0;
    reg [31:0] sda_delay_counter        = 32'h0;
    reg [31:0] scl_delay_counter_prev   = 32'h0;
    reg [31:0] sda_delay_counter_prev   = 32'h0;

    reg [1:0] scl_buff              = IIC_IDLE;
    reg [1:0] sda_buff              = IIC_IDLE;
    
    // Output variables from state machine
    reg [7:0]   device_address  = 8'h0;     // Store device address after a start or repeat-start
    reg [7:0]   data_byte       = 8'h0;     // Store last data byte transmitted
    reg [3:0]   bit_counter     = 4'h0;     // Counter for numbe rof bits received per byte
    reg [31:0]  word_counter    = 32'h0;    // Counter for number of words recieved after start or repeat-start
    reg [31:0]  error_reg       = 32'h0;    // Timing errors caught during state transistions
    reg         ack_bit         = 1'b0;     // ACK/NACK bit at end of each byte transfer
    
    // State machine variables, initialized to STATE_RESET state
    reg [3:0] current_state         = STATE_RESET;
    reg [3:0] next_state            = STATE_IDLE;
    
    assign ack_o = ack_bit;
    assign address_o = device_address;
    assign data_o = data_byte;
    assign state_o = current_state;
    assign error_o = error_reg;
    
    // Update state, input buffers, and counters
    always @(posedge clk_i) begin
        if(reset_i == 1'b0) begin
            current_state <= STATE_RESET;
            scl_delay_counter <= 32'h0;
            sda_delay_counter <= 32'h0;
            scl_buff <= IIC_IDLE;
            sda_buff <= IIC_IDLE;
        end
        else begin
            // Update current state
            current_state <= next_state;
            
            // Update signal buffers for edge detection
            scl_buff <= { scl_buff[0], i2c_scl_i };
            sda_buff <= { sda_buff[0], i2c_sda_i };
            
            // Reset delay counter when signal transitions
            // Increment unless delay_counter = max_u32
            if(scl_buff[0] != i2c_scl_i) begin
                scl_delay_counter       <= 32'h0;
                scl_delay_counter_prev  <= scl_delay_counter;
            end else if(~scl_delay_counter) begin
                scl_delay_counter <= scl_delay_counter + 1;
            end
            
            if(sda_buff[0] != i2c_sda_i) begin
                sda_delay_counter       <= 32'h0;
                sda_delay_counter_prev  <= sda_delay_counter;
            end else if(~sda_delay_counter) begin
                sda_delay_counter <= sda_delay_counter + 1;
            end
        end
    end
    
    // Change state logic
    always @(current_state, scl_buff, sda_buff) begin
    case(current_state)
    
    
    STATE_RESET:
    begin
        next_state      <= STATE_IDLE;
        device_address  <= 8'h0;
        data_byte       <= 8'h0;
        bit_counter     <= 4'h0;
        word_counter    <= 32'h0;
        error_reg       <= 32'h0;
        ack_bit         <= 1'b0;
    end
    
    
    STATE_IDLE: 
    begin
        // START condition, go to START
        if(sda_buff == FALLING_EDGE) begin
            if(sda_delay_counter_prev < T_BUF) begin
                next_state <= STATE_ERROR;
                error_reg <= error_reg | T_BUF_ERROR_CODE;
            end else begin
                next_state <= STATE_START;
            end
        end
        
        // Set state output variables
        // While in STATE_IDLE all output variables are reset
        device_address  <= 8'h0;
        data_byte       <= 8'h0;
        bit_counter     <= 4'h0;
        word_counter    <= 32'h0;
        ack_bit         <= 1'b0;
    end
    
    
    STATE_START: 
    begin
        // State change logic
        if(scl_buff == FALLING_EDGE) begin
            if(sda_delay_counter < T_HDSTA) begin
                next_state <= STATE_ERROR;
                error_reg <= error_reg | T_HDSTA_ERROR_CODE;
            end else begin
                next_state <= STATE_BYTE_START;
            end
        end
        
        // Set state output variables
        // While in STATE_START all output variables are reset
        device_address  <= 8'h0;
        data_byte       <= 8'h0;
        bit_counter     <= 4'h0;
        word_counter    <= 32'h0;
        ack_bit         <= 1'b0;
    end
    
    
    STATE_BYTE_START: 
    begin
        // State change logic
        if(scl_buff == RISING_EDGE) begin
            if(sda_delay_counter < T_SUDAT) begin
                next_state <= STATE_ERROR;
                error_reg <= error_reg | T_SUDAT_ERROR_CODE;
            end else begin
                next_state <= STATE_HIGH_DATA;
                
                // Set state output variables
                data_byte   <= {7'h0, i2c_sda_i};   // Update data_byte with first bit when leaving state
                bit_counter <= bit_counter + 1;     // Increment bit_counter when leaving state
            end
        end        
    end
    
    
    STATE_HIGH_DATA: 
    begin
        // State change logic
        if(scl_buff == FALLING_EDGE) begin
            next_state <= STATE_LOW_DATA;
        end else if((sda_buff == RISING_EDGE) || (sda_buff == FALLING_EDGE)) begin
            next_state <= STATE_ERROR;
            error_reg <= error_reg | SDA_TRANS_ERROR_CODE;
        end
    end
    
    
    STATE_LOW_DATA: 
    begin
        // State change logic
        if(scl_buff == RISING_EDGE) begin
            if(sda_delay_counter < T_SUDAT) begin
                next_state <= STATE_ERROR;
                error_reg <= error_reg | T_SUDAT_ERROR_CODE;
            end else begin
                // Receiving data bits
                if(bit_counter < IIC_BITS_PER_WORD) begin
                    next_state <= STATE_HIGH_DATA;
                    data_byte   <= {data_byte[6:0], i2c_sda_i}; // Update data_byte with current sda value
                    bit_counter <= bit_counter + 1;             // Increment bit_counter
                
                // Receiving ACK/NACK bit
                end else if(bit_counter == IIC_BITS_PER_WORD) begin
                    next_state <= STATE_HIGH_DATA;
                    ack_bit <= i2c_sda_i;               // Update ack_bit with current sda value
                    bit_counter <= bit_counter + 1;     // Increment bit_counter
                    word_counter <= word_counter + 1;   // Increment word_counter
                    
                    if(word_counter == 0) begin
                        device_address <= data_byte;
                    end
                    
                // Word end reached
                end else begin
                    next_state <= STATE_BYTE_END;
                end
            end
        end  
    end
    
    
    STATE_BYTE_END: 
    begin
        // Next data word in transaction, no RSTART or STOP
        if(scl_buff == FALLING_EDGE) begin
            if(sda_delay_counter < T_HDSTA) begin
                next_state <= STATE_ERROR;
                error_reg <= error_reg | T_HDSTA_ERROR_CODE;
            end else begin
                next_state <= STATE_BYTE_START;
            end
        // RSTART condition, go to START
        end else if(sda_buff == FALLING_EDGE) begin
            if(scl_delay_counter < T_SUSTA) begin
                next_state <= STATE_ERROR;
                error_reg <= error_reg | T_SUSTA_ERROR_CODE;
            end else begin
                next_state <= STATE_START;
            end
        // STOP conditoin, go to IDLE
        end else if(sda_buff == RISING_EDGE) begin
            if(scl_delay_counter < T_SUSTO) begin
                next_state <= STATE_ERROR;
                error_reg <= error_reg | T_SUSTO_ERROR_CODE;
            end else begin
                next_state <= STATE_IDLE;
            end
        end
    end   


    // Stay in STATE_ERROR until state machine is reset
    STATE_ERROR:
    begin
        next_state <= STATE_ERROR;
    end    
    
    default begin
        next_state <= STATE_ERROR;
    end
    
    endcase
    
    end
    
    
endmodule
