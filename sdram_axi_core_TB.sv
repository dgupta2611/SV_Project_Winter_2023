`define DELAY(n) repeat(n) @(posedge clk_i)

module sdram_axi_core_TB();

`timescale 1ns / 1ps

import definitions::*;

// Controller Inputs
logic           clk_i;
logic           rst_i;
logic  [  3:0]  inport_wr_i = 0;
logic           inport_rd_i = 0;
// logic  [  7:0]  inport_len_i;
logic  [ 31:0]  inport_addr_i = 0;
logic  [ 31:0]  inport_write_data_i;
// logic  [ 15:0]  sdram_data_input_i;

// Controller Outputs
logic          inport_accept_o;
logic          inport_ack_o;
logic          inport_error_o;
logic [ 31:0]  inport_read_data_o;
logic          sdram_clk_o;
logic          sdram_cke_o;
logic          sdram_cs_o;
logic          sdram_ras_o;
logic          sdram_cas_o;
logic          sdram_we_o;
logic [  1:0]  sdram_dqm_o;
logic [ 12:0]  sdram_addr_o;
logic [  1:0]  sdram_ba_o;
// logic [ 15:0]  sdram_data_output_o;
logic          sdram_data_out_en_o;

// Bus
wire  [15:0]   sdram_data_bus_io;

wire [ 15:0] Dq;

sdram_axi_core sdram_axi_controller (.*);
mt48lc16m16a2  MEM_mt48lc16m16a2    (.Dq     (sdram_data_bus_io), 
                                     .Addr   (sdram_addr_o), 
                                     .Ba     (sdram_ba_o), 
                                     .Clk    (sdram_clk_o), 
                                     .Cke    (sdram_cke_o), 
                                     .Cs_n   (sdram_cs_o), 
                                     .Ras_n  (sdram_ras_o), 
                                     .Cas_n  (sdram_cas_o), 
                                     .We_n   (sdram_we_o), 
                                     .Dqm    (sdram_dqm_o));

data_rand #(16) sdram2cont_data;
data_rand #(32) intf2cont_data;

task WriteMem(input [3:0] wr_mask, input [31:0] wr_addr);
    // @(posedge clk_i) begin
        inport_wr_i   = wr_mask;
        inport_addr_i = wr_addr;
    // end
    wait(inport_accept_o);
    wait(~inport_accept_o);
    inport_wr_i = '0;
    
endtask

task ReadMem(input [31:0] rd_addr);
    // @(posedge clk_i) begin
        inport_rd_i   = 1;
        inport_addr_i = rd_addr;
    // end

    // @(posedge clk_i) inport_rd_i   = 0;

    wait(inport_accept_o);
    wait(~inport_accept_o);
    inport_rd_i   = 0;
    
endtask

initial  begin
    clk_i = 0;
    forever #(CYCLE_TIME_NS/2) clk_i = ~clk_i;
end

initial begin

    sdram2cont_data = new();
    intf2cont_data  = new();

    rst_i = 1; 
    repeat(2) @(posedge clk_i); 
    rst_i = 0;

    #((SDRAM_START_DELAY+200)*CYCLE_TIME_NS);
    $display("SDRAM Ready");

    WriteMem(4'hf, '0);
    WriteMem(4'hf, 32'd4);
    WriteMem(4'hf, 32'd8);
    // `DELAY(5);
    ReadMem('0);
    ReadMem(32'd4);
    ReadMem(32'd8);

    repeat(10) @(posedge clk_i);

    $stop;

end

// Driving the BUS

logic [15:0] rand_data_sdram2cont;

always @(posedge clk_i) begin

    assert (sdram2cont_data.randomize());
    assert (intf2cont_data.randomize());

    // sdram_data_input_i = sdram2cont_data.data;
    rand_data_sdram2cont = sdram2cont_data.data;
    inport_write_data_i  = intf2cont_data.data;
end

// assign sdram_data_bus_io   = ~sdram_data_out_en_o ? rand_data_sdram2cont : 'bz;

endmodule