interface controller-memory;

logic          sdram_clk_o;
logic          sdram_cke_o;
logic          sdram_cs_o;
logic          sdram_ras_o;
logic          sdram_cas_o;
logic          sdram_we_o;
logic [  1:0]  sdram_dqm_o;
logic [ 12:0]  sdram_addr_o;
logic [  1:0]  sdram_ba_o;
//logic [ 15:0]  sdram_data_input_i,
//logic [ 15:0]  sdram_data_logic_o;
logic          sdram_data_out_en_o;


modport Controller(output sdram_clk_o,sdram_cke_o,sdram_cs_o,sdram_ras_o,sdram_cas_o,sdram_we_o,
				   output[1:0] sdram_dqm_o,
				   output[12:0] sdram_addr_o,
				   output[1:0] sdram_ba_o,
				   //inout [15:0] sdram_data_logic_o,
				   output sdram_data_out_en_o);

modport Memory(input sdram_clk_o,sdram_cke_o,sdram_cs_o,sdram_ras_o,sdram_cas_o,sdram_we_o,
				   input[1:0] sdram_dqm_o,
				   input[12:0] sdram_addr_o,
				   input[1:0] sdram_ba_o,
				   //inout [15:0] sdram_data_logic_o,
				   input sdram_data_out_en_o);

endinterface