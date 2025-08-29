// Wishbone bus system interconnect (syscon)
// for multiple master, multiple slave bus
// max 8 masters and 16 slaves
// Mike Baird

interface wishbone_bus_syscon_if #(int num_masters = 8, int num_slaves = 16,
                                   int data_width = 32, int addr_width = 32) ();
import wishbone_pkg::*;


  // wishbone common signals
  bit clk;
  bit rst;
  bit [num_slaves-1:0] irq;  // slave interrupt vector
  // wishbone master outputs
  logic [data_width-1:0]  m_wdata[num_masters];
  logic [addr_width-1:0]  m_addr [num_masters];
  bit m_cyc [num_masters];
  bit m_lock[num_masters];
  bit m_stb [num_masters];
  bit m_we  [num_masters];
  bit m_ack [num_masters];
  bit [7:0] m_sel[num_masters];

  // wishbone master inputs
  bit m_err;
  bit m_rty;
  logic [data_width-1:0]  m_rdata;

  // wishbone slave inputs
  logic [data_width-1:0]  s_wdata;
  logic [addr_width-1:0]  s_addr;
  bit [7:0]  s_sel;
  bit s_cyc;
  bit [num_slaves-1:0]s_stb; //only input not shared since it is the select
  bit s_we;


  // wishbone slave outputs
  logic [data_width-1:0] s_rdata[num_slaves];
  bit s_err[num_slaves];
  bit s_rty[num_slaves];
  bit s_ack[num_slaves];

  //Wishbone Revision B.3.  Typically not used
  bit [2:0]  m_cti[num_masters];   // Cycle Type Identifier
  bit [1:0]  m_bte[num_masters];   // Burst Type Extension
  bit [2:0]  s_cti;   // Cycle Type Identifier
  bit [1:0]  s_bte;   // Burst Type Extension


//clk generation
//--------------------------------
//  always  #12.5 clk = ~ clk;   // 2*12.5 ns -> 40 MHz
  always  #10 clk = ~ clk;   // 2*10 ns -> 50 MHz

// reset generation
//--------------------------------
 initial begin
   rst = 1;
   repeat(5) @ (posedge clk) ;
   rst = 0;
 end

// wishbone bus arbitration logic
//--------------------------------
// A master requests the bus by raising his cyc signal
  enum {GRANT0,GRANT1,GRANT2,GRANT3,GRANT4,GRANT5,GRANT6,GRANT7} state, next_state;
// note that the states match the master's value. ie GRANT1 has a value of 1 and
// indicates that master 1 is granted the bus.
  bit gnt[num_masters];

  always @ (posedge clk)
    if(rst) begin
      state <= #1 GRANT0;
      foreach(gnt[i]) gnt[i] <= #1 0;  // clear any grant
      gnt[0] <= #1 1;  // set inital grant
    end else
      state <= #1 next_state;

  always @ (state) begin
    foreach(gnt[i]) gnt[i] = 0;
    gnt[state] = 1;
  end

  always @ (state or m_cyc[0] or m_cyc[1] or m_cyc[2]
            or m_cyc[3] or m_cyc[4] or m_cyc[5] or m_cyc[6] or m_cyc[7] ) begin
    next_state = state; // Default - keep state
    case (state)
      GRANT0:
        if(!m_cyc[0]) // if request is dropped arbitrate
            arbitrate(0);  // go to next state with a request
      GRANT1:
        if(!m_cyc[1]) // if request is dropped arbitrate
            arbitrate(1);  // go to next state with a request
      GRANT2:
        if(!m_cyc[2]) // if request is dropped arbitrate
            arbitrate(2);  // go to next state with a request
      GRANT3:
        if(!m_cyc[3]) // if request is dropped arbitrate
            arbitrate(3);  // go to next state with a request
      GRANT4:
        if(!m_cyc[4]) // if request is dropped arbitrate
            arbitrate(4);  // go to next state with a request
      GRANT5:
        if(!m_cyc[5]) // if request is dropped arbitrate
            arbitrate(5);  // go to next state with a request
      GRANT6:
        if(!m_cyc[6]) // if request is dropped arbitrate
            arbitrate(6);  // go to next state with a request
      GRANT7:
        if(!m_cyc[7]) // if request is dropped arbitrate
            arbitrate(7);  // go to next state with a request
      default: begin
//        `uvm_error("WB_SYSCON_ARB", "Illegal state in Wishbone Arbiter reached" )
//        next_state = GRANT0;
        foreach(gnt[i]) gnt[i] <= #1 0;  // clear any grant
        gnt[0] <= #1 1;  // set inital grant
      end
    endcase
  end

  function void arbitrate(int last_grant);
    for (int i=0; i<num_masters; i++) begin
      //increment last_grant so start check with next master
      last_grant++;
      if(last_grant == num_masters) //check for need to wrap
        last_grant = 0; //wrap if necessary
      if(m_cyc[last_grant] == 1) begin  //request?
        $cast(next_state, last_grant);  // go to granted master's equivalent state
        return;
      end
    end
  endfunction

//Slave address decode
//--------------------------------
// slave memory map
// Note:  Wishbone is byte addressable. The stb signal is what indicates to a
// slave device it has been selected
// each slave mapped to 268 Mbytes (268,435,456 bytes) of address space
// Each slave uses addr[19:00] internally, addr[31:28] is used for slave select
// slave 0:  00000000 - 0fffffff
// slave 1:  10000000 - 1fffffff
// slave 2:  20000000 - 2fffffff
// slave 3:  30000000 - 3fffffff
// and so forth

// the stb input to the slave is the slave select
always @ (m_addr[state][31:28] or m_stb[state] or state ) begin
  s_stb = 0; // clear all strobes
  // set selected slave strobe to master strobe
  s_stb[m_addr[state][31:28]] = m_stb[state];
end

// bus muxing logic
//--------------------------------
  // Master to slave connections
  always @ (state or m_wdata[state])
   s_wdata = m_wdata[state];

  always @ (state or m_addr[state])
   s_addr = m_addr[state];

  always @ (state or m_sel[state])
   s_sel = m_sel[state];

  always @ (state or m_cyc[state])
   s_cyc = m_cyc[state];

  always @ (state or m_stb[state])
   s_stb[m_addr[state][31:28]] = m_stb[state];

  always @ (state or m_we[state])
   s_we = m_we[state];

  always @ (state or m_cti[state])
   s_cti = m_cti[state];

  always @ (state or m_bte[state])
   s_bte = m_bte[state];

  //slave to master connections
  always @ (s_rdata[m_addr[state][31:28]])
   m_rdata = s_rdata[m_addr[state][31:28]];

  always @ (s_ack[m_addr[state][31:28]])
   m_ack[state] = s_ack[m_addr[state][31:28]];

  always @ (s_err[m_addr[state][31:28]])
   m_err = s_err[m_addr[state][31:28]];

  always @ (s_rty[m_addr[state][31:28]])
   m_rty = s_rty[m_addr[state][31:28]];

  function automatic void bus_reset();
    m_cyc[1] = 0;
    m_stb[1] = 0;
  endfunction

// --------------------------------------------------------------
//  BFM interface

// ---------- Driver

  //READ 1 or more cycles
  task automatic wb_read_cycle(output logic[31:0] data,
       input bit [31:0] adr, int unsigned count = 1, byte_sel = 4'b1111);
    logic [31:0] temp_addr = adr;
    @ (posedge clk) #1;  // sync to clock edge + 1 time step
    for(int i = 0; i<count; i++) begin
      if(rst) begin
        bus_reset();  // clear everything
        return; //exit if reset is asserted
      end
      m_addr[1] <= temp_addr;
      m_we[1]  <= 0;  // read
      m_sel[1] <= byte_sel;
      m_cyc[1] <= 1;
      m_stb[1] <= 1;
      @ (posedge clk)
      while (!(m_ack[1] & gnt[1])) @ (posedge clk);
      data = m_rdata;  // get data
      temp_addr =  temp_addr + 4;  // byte address so increment by 4 for word addr
    end
    m_cyc[1] <= 0;
    m_stb[1] <= 0;
    while (m_ack[1]) @ (posedge clk); // Wait for ack to de-assert
  endtask

  //WRITE  1 or more write cycles
  task automatic wb_write_cycle(input logic[31:0] data,
          bit [31:0] adr, int unsigned count = 1, byte_sel = 4'b1111);
    logic [31:0] temp_addr = adr;
    @ (posedge clk) #1;  // sync to clock edge + 1 time step
    for(int i = 0; i<count; i++) begin
      if(rst) begin
        bus_reset();  // clear everything
        return; //exit if reset is asserted
      end
      m_wdata[1] <= data;
      m_addr[1] <= temp_addr;
      m_we[1]  <= 1;  //write
      m_sel[1] <= byte_sel;
      m_cyc[1] <= 1;
      m_stb[1] <= 1;
      @ (posedge clk)
      while (!(m_ack[1] & gnt[1])) @ (posedge clk);
      temp_addr =  temp_addr + 4;  // byte address so increment by 4 for word addr
    end
    m_cyc[1] <= 0;
    m_stb[1] <= 0;
    while (m_ack[1]) @ (posedge clk); // Wait for ack to de-assert
  endtask

  //RMW ( read-modify_write)
  task automatic wb_rmw_cycle(ref wb_txn req_txn);
//    `uvm_info($sformatf("WB_SYSCON_IF"),
//                    "Wishbone RMW instruction not implemented yet",UVM_LOW )
  endtask

  task automatic wb_irq(output logic[31:0] irq_vec);
    @ (posedge clk) #1;  // sync to clock edge + 1 time step
    wait(irq);
    irq_vec = irq;
  endtask


  // ---------- Monitor

//  task automatic monitor_txn(ref wb_txn txn);
  task automatic monitor_txn(output logic[31:0] data,
       output bit [31:0] adr, wb_txn_t txn_type);
    forever begin
      @ (posedge clk);
      if(s_cyc &&
        (s_stb[0] | s_stb[1] | s_stb[2]) ) begin
        adr = s_addr; // get address

        if(s_we)  begin // is it a write?
          data = s_wdata;  // get datSa
          txn_type = WRITE; // set op type

          while (!(s_ack[0] | s_ack[1] | s_ack[2]))
            @ (posedge clk); // wait for ack

          if(!(s_stb[0] | s_stb[1] | s_stb[2])) //not a block write?
            while ((s_ack[0] | s_ack[1] | s_ack[2]))
              @ (posedge clk); // wait for !ack
        end
        else begin
          txn_type = READ; // set op type
          case (1) //Nope its a read, get data from correct slave
            s_stb[0]:  begin
                while (!(s_ack[0])) @ (posedge clk); // wait for ack
                data = s_rdata[0];  // get data
                if(!(s_stb[0])) //not a block read?
                  while ((s_ack[0])) @ (posedge clk); // wait for !ack
              end
            s_stb[1]:  begin
                while (!(s_ack[1])) @ (posedge clk); // wait for ack
                data = s_rdata[1];  // get data
                if(!(s_stb[1])) //not a block read?
                  while ((s_ack[1])) @ (posedge clk); // wait for !ack
              end
            s_stb[2]:  begin
                while (!(s_ack[2])) @ (posedge clk); // wait for ack
                data = s_rdata[2];  // get data
                if(!(s_stb[2])) //not a block read?
                  while ((s_ack[2])) @ (posedge clk); // wait for !ack
              end
          endcase
        end // if write or read
        return;
      end // if valid transaction
    end // forever
  endtask


endinterface
