`define DELAY(n) repeat(n) @(posedge clk_i)

module sdram_core_TB();

`timescale 1ns / 1ps

import definitions::*;

// Controller Inputs
logic           clk_i;
logic           rst_i;
logic  [  3:0]  inport_wr_i = 0;
logic           inport_rd_i = 0;
logic  [ 31:0]  inport_addr_i = 0;
logic  [ 31:0]  inport_write_data_i;

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
logic          sdram_data_out_en_o;

// Bus
wire  [15:0]   sdram_data_bus_io;


/////////////////////////////// Instantiations ////////////////////////////////
sdram_core sdram_controller (.*);
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

bind sdram_core sdram_assertions ramAssert (
    // Inputs
    clk_i,
    rst_i,
    inport_wr_i,
    inport_rd_i,
    inport_addr_i,
    inport_write_data_i,
    
    // Outputs
    inport_accept_o,
    inport_ack_o,
    inport_error_o,
    inport_read_data_o,
    sdram_clk_o,
    sdram_cke_o,
    sdram_cs_o,
    sdram_ras_o,
    sdram_cas_o,
    sdram_we_o,
    sdram_dqm_o,
    sdram_addr_o,
    sdram_ba_o,
    sdram_data_out_en_o,

    // Bus
    sdram_data_bus_io,

    // Internal states
    refresh_timer_q,
    refresh_q,
    rd_q,
    state_q,
    row_open_q,
    active_row_q);

///////////////////////////////////////////////////////////////////////////////

////////////////////////////// Declarations ///////////////////////////////////
genvar i;
ref_mem memModel;

logic intf2cont_datSample;

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

task automatic WriteMem(input [3:0] mask, input [31:0] wr_addr, input [31:0] wr_data, const ref ref_mem memModel);

    logic [35:0] wd;

    assert(|mask) else begin
        $warning("%t Using WriteMem task with a write mask = 'd0", $time);
        return; 
    end

    inport_wr_i   = mask;
    inport_addr_i = wr_addr;
    inport_write_data_i = wr_data;

    // Updating the associative array with the data        
    memModel.write(wr_addr[24:2], wr_data, mask);

    // Making sure the reference memory got updated
    wd = memModel.read(wr_addr[24:2]);
    $display("Memory Model written for Address = %h Word 1 = %h Word 0 = %h Mask = %h", wr_addr, 
                                                                                        wd[31:16], 
                                                                                        wd[15:0], 
                                                                                        wd[35:32]);

    wait(inport_accept_o);  // WRITE0
    wait(~inport_accept_o); // WRITE1

    inport_wr_i = '0;
    
endtask

task automatic ReadMem(input [31:0] rd_addr, const ref ref_mem memModel);


    inport_rd_i   = 1;
    inport_addr_i = rd_addr;

    wait(inport_accept_o); // READ

    refMemReadSuccess = memModel.M.exists(rd_addr[24:2]);

    if(~refMemReadSuccess) 
        $warning("Trying to access unwritten Memory location");

    if(refMemReadSuccess) 
        {refMemReadMask, refMemReadData} = memModel.read(rd_addr[24:2]);

    inport_rd_i   = 0;

    wait(~inport_accept_o);
    
endtask

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////// Assertions to check RD data against Ref Mem Data ///////////////////////////////

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

    int numOps_WrHeavy;
    int numOps_Random;

    logic [31:0] fullAddr;
    logic [3:0]  mask;
    logic [31:0] wrData;

    int write;
    int delay;

    data_rand #(32) randData;
    addr_rand #(32) randAddr;
    wrBytes         randMask;
    ops_rand  #(80) wr80Percent;
    ops_rand  #(50) wr50Percent;
    delay_rand      randDelay;

    // sdram2cont_data = new();
    randData        = new();
    memModel        = new();
    randAddr        = new();
    wr80Percent     = new();
    wr50Percent     = new();
    randMask        = new();
    randDelay       = new();

    numOps_WrHeavy = 550;
    numOps_Random  = 450;

    intf2cont_datSample = 1;

    rst_i = 1; 
    repeat(2) @(posedge clk_i); 
    rst_i = 0;

    #((SDRAM_START_DELAY+200)*CYCLE_TIME_NS);
    $display("SDRAM Ready");

    fullAddr = '0;    assert(randData.randomize()) else $error("Data randomization failed"); wrData = randData.data; WriteMem(4'hf, fullAddr, wrData, memModel); 
    fullAddr = 32'd4; assert(randData.randomize()) else $error("Data randomization failed"); wrData = randData.data; WriteMem(4'hf, fullAddr, wrData, memModel);
    fullAddr = 32'd8; assert(randData.randomize()) else $error("Data randomization failed"); wrData = randData.data; WriteMem(4'hf, fullAddr, wrData, memModel);
    
    // `DELAY(5);
    fullAddr = '0   ; ReadMem(fullAddr, memModel);
    fullAddr = 32'd4; ReadMem(fullAddr, memModel);
    fullAddr = 32'd8; ReadMem(fullAddr, memModel);


    while(numOps_WrHeavy) begin
        assert(randData.randomize())    else $error("Data randomization failed");
        assert(randAddr.randomize())    else $error("Addr randomization failed");
        assert(randMask.randomize())    else $error("Mask randomization failed");
        assert(wr80Percent.randomize()) else $error("wr80 randomization failed");
        assert(randDelay.randomize())   else $error("Delay randomization failed");

        wrData   = randData.data;
        fullAddr = randAddr.addr;
        mask     = randMask.mask;
        write    = wr80Percent.issueWr;
        delay    = randDelay.delay;

        if(write) begin
            WriteMem(mask, fullAddr, wrData, memModel);
        end
        else begin
            ReadMem(fullAddr, memModel);    
        end

         #(delay);

        numOps_WrHeavy -= 1;
    end

    while(numOps_Random) begin
        assert(randData.randomize())    else $error("Data randomization failed");
        assert(randAddr.randomize())    else $error("Addr randomization failed");
        assert(randMask.randomize())    else $error("Mask randomization failed");
        assert(wr50Percent.randomize()) else $error("wr50 randomization failed");
        assert(randDelay.randomize())   else $error("Delay randomization failed");

        wrData   = randData.data;
        fullAddr = randAddr.addr;
        mask     = randMask.mask;
        write    = wr50Percent.issueWr;
        delay    = randDelay.delay;

        if(write) begin
            WriteMem(mask, fullAddr, wrData, memModel);
        end
        else begin
            ReadMem(fullAddr, memModel);    
        end

         #(delay);

        numOps_Random -= 1;
    end

    repeat(10) @(posedge clk_i);

    $stop;

end
////////////////////////////////////////////////////////////////////////////////////

endmodule