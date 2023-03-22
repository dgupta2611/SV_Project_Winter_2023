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


/////////////////////////////// Instantiations ////////////////////////////////
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

///////////////////////////////////////////////////////////////////////////////

////////////////////////////// Declarations ///////////////////////////////////
genvar i;
ref_mem memModel;
logic [31:0] fullAddr;

logic intf2cont_datSample;

// data_rand #(16) sdram2cont_data;
data_rand #(32) intf2cont_data;
logic [31:0] rand_data_intf2cont;

logic [31:0] refMemReadData;
logic [3:0]  refMemReadMask;
bit          refMemReadSuccess;

///////////////////////////////////////////////////////////////////////////////

////////////////////////// Setting up the clock //////////////////////////////
initial  begin
    clk_i = 0;
    forever #(CYCLE_TIME_NS/2) clk_i = ~clk_i;
end

///////////////////////////////////////////////////////////////////////////////

/////////////////////////// Read/Write Tasks////////////////////////////////////////////////////

task automatic WriteMem(input [3:0] wr_mask, input [31:0] wr_addr, const ref ref_mem memModel);

    logic [35:0] wd;

    assert(|wr_mask) else begin
        $warning("%t Using WriteMem task with a write mask = 'd0", $time);
    end

    inport_wr_i   = wr_mask;
    inport_addr_i = wr_addr;
    intf2cont_datSample = 1;

    @(posedge clk_i) begin
        intf2cont_datSample = 0;  // At the edge, sample random inport_write_data_i data and then retain
        
        memModel.write(wr_addr[24:2], rand_data_intf2cont, wr_mask);

        // Making sure the reference memory got updated
        wd = memModel.read(wr_addr[24:2]);
        $display("Memory Model written for Address = %h Word 1 = %h Word 0 = %h Mask = %h", wr_addr, 
                                                                                            wd[31:16], 
                                                                                            wd[15:0], 
                                                                                            wd[35:32]);
    end

    wait(inport_accept_o);
    wait(~inport_accept_o);

    inport_wr_i = '0;
    
endtask

task automatic ReadMem(input [31:0] rd_addr, const ref ref_mem memModel);


    inport_rd_i   = 1;
    inport_addr_i = rd_addr;

    wait(inport_accept_o);

    refMemReadSuccess = memModel.M.exists(rd_addr[24:2]);

    if (~refMemReadSuccess) 
        $warning("Trying to access unwritten Memory location");

    if(refMemReadSuccess) 
        {refMemReadMask, refMemReadData} = memModel.read(rd_addr[24:2]);

    wait(~inport_accept_o);

    inport_rd_i   = 0;
    
endtask

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////// Assertions to check RD data against Ref Mem Data ///////////////////////////////
always_ff @(posedge clk_i) begin
    if(inport_ack_o && ~sdram_data_out_en_o) begin
        $display("Memory Model Read for Address = %h Word 1 = %h Word 0 = %h Mask = %h \n", 
                  $past(inport_addr_i,         SDRAM_READ_LATENCY), 
                  $past(refMemReadData[31:16], SDRAM_READ_LATENCY), 
                  $past(refMemReadData[15:0],  SDRAM_READ_LATENCY), 
                  $past(refMemReadMask,        SDRAM_READ_LATENCY));
    end
end

for (i = 0; i < 4; i++) begin
    
    property refMem_hwMem_Byte_Match_p;
        @(posedge clk_i) disable iff(rst_i)
            (inport_ack_o && ~sdram_data_out_en_o && 
             $past(refMemReadSuccess, SDRAM_READ_LATENCY) && $past(refMemReadMask[i], SDRAM_READ_LATENCY)) |-> // antecedent

            ($past(refMemReadData[8*i +: 8], SDRAM_READ_LATENCY) == inport_read_data_o[8*i +: 8]);
    endproperty

    refMem_hwMem_Byte_Match_a: assert property(refMem_hwMem_Byte_Match_p);

end

//////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////// Main Simulation Block //////////////////////////////
initial begin

    intf2cont_datSample = 1;

    // sdram2cont_data = new();
    intf2cont_data  = new();

    memModel        = new();

    rst_i = 1; 
    repeat(2) @(posedge clk_i); 
    rst_i = 0;

    #((SDRAM_START_DELAY+200)*CYCLE_TIME_NS);
    $display("SDRAM Ready");

    fullAddr = '0;    WriteMem(4'hf, fullAddr, memModel); 
    fullAddr = 32'd4; WriteMem(4'hf, fullAddr, memModel);
    fullAddr = 32'd8; WriteMem(4'hf, fullAddr, memModel);
    
    // `DELAY(5);
    fullAddr = '0   ; ReadMem(fullAddr, memModel);
    fullAddr = 32'd4; ReadMem(fullAddr, memModel);
    fullAddr = 32'd8; ReadMem(fullAddr, memModel);

    // ReadMem(32'd12);

    repeat(10) @(posedge clk_i);

    $stop;

end
////////////////////////////////////////////////////////////////////////////////////

////////////////// Driving the wr BUS from interface //////////////////////////////
// logic [15:0] rand_data_sdram2cont;

always @(posedge clk_i) begin

    // assert (sdram2cont_data.randomize());
    assert (intf2cont_data.randomize()) else begin
       $error("Data Randomization failed"); 
    end

    // sdram_data_input_i = sdram2cont_data.data;
    // rand_data_sdram2cont = sdram2cont_data.data;

    // Implicit type cast from class definitions::data_rand to logic [31:0]
    rand_data_intf2cont  = intf2cont_datSample ? intf2cont_data.data : rand_data_intf2cont;
    inport_write_data_i  = rand_data_intf2cont;
end

// assign sdram_data_bus_io   = ~sdram_data_out_en_o ? rand_data_sdram2cont : 'bz;
/////////////////////////////////////////////////////////////////////////////////////

endmodule