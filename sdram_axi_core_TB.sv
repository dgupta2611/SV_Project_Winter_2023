//-----------------------------------------------------------------
//                    SDRAM Controller (AXI4)
//                           V1.0
//                     Ultra-Embedded.com
//                     Copyright 2015-2019
//
//                 Email: admin@ultra-embedded.com
//
//                         License: GPL
// If you would like a version with a more permissive license for
// use in closed source commercial applications please contact me
// for details.
//-----------------------------------------------------------------
//
// This file is open source HDL; you can redistribute it and/or 
// modify it under the terms of the GNU General Public License as 
// published by the Free Software Foundation; either version 2 of 
// the License, or (at your option) any later version.
//
// This file is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public 
// License along with this file; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
// USA
//-----------------------------------------------------------------

//-----------------------------------------------------------------
//                          Generated File
//-----------------------------------------------------------------

module sdram_axi_core_TB();

import definitions::*;

    // Inputs
    logic           clk_i;
    logic           rst_i;
    logic  [  3:0]  inport_wr_i = 0;
    logic           inport_rd_i = 0;
    logic  [  7:0]  inport_len_i;
    logic  [ 31:0]  inport_addr_i = 0;
    logic  [ 31:0]  inport_write_data_i;
    logic  [ 15:0]  sdram_data_input_i;

    // Outputs
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
    logic [ 15:0]  sdram_data_output_o;
    logic          sdram_data_out_en_o;


sdram_axi_core sdram_axi_controller (.*);

initial  begin
    clk_i = 0;
    forever #(CYCLE_TIME_NS/2) clk_i = ~clk_i;
end

initial begin
    rst_i = 1; 
    repeat(2) @(posedge clk_i); 
    rst_i = 0;

    #((SDRAM_START_DELAY+200)*CYCLE_TIME_NS);
    $display("SDRAM Ready");

    inport_rd_i = 1;
    repeat(2) @(posedge clk_i); 
    inport_rd_i = 0;
    
    repeat(20) @(posedge clk_i);
    
    $stop;

end

endmodule