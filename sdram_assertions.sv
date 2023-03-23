module sdram_assertions
import definitions::*;
  (
    // Inputs
    input           clk_i,
    input           rst_i,
    input  [  3:0]  inport_wr_i,
    input           inport_rd_i,
    input  [ 31:0]  inport_addr_i,
    input  [ 31:0]  inport_write_data_i,
    
    // Outputs
    input          inport_accept_o,
    input          inport_ack_o,
    input          inport_error_o,
    input [ 31:0]  inport_read_data_o,
    input          sdram_clk_o,
    input          sdram_cke_o,
    input          sdram_cs_o,
    input          sdram_ras_o,
    input          sdram_cas_o,
    input          sdram_we_o,
    input [  1:0]  sdram_dqm_o,
    input [ 12:0]  sdram_addr_o,
    input [  1:0]  sdram_ba_o,
    input          sdram_data_out_en_o,

    // Bus
    input  [15:0]   sdram_data_bus_io,

    // Internal states
    input  [16:0] refresh_timer_q,
    input refresh_q,
    input  [SDRAM_READ_LATENCY+1:0]  rd_q,
    input  [3:0]     state_q,
    input [SDRAM_BANKS-1:0]  row_open_q,
    input [SDRAM_ROW_W-1:0]  active_row_q[0:SDRAM_BANKS-1]
  );

  //-----------------------------------------------------------------
  // Defines / Local params
  //-----------------------------------------------------------------
  
  localparam CMD_W             = 4;
  localparam CMD_NOP           = 4'b0111;
  localparam CMD_ACTIVE        = 4'b0011;
  localparam CMD_READ          = 4'b0101;
  localparam CMD_WRITE         = 4'b0100;
  localparam CMD_TERMINATE     = 4'b0110;
  localparam CMD_PRECHARGE     = 4'b0010;
  localparam CMD_REFRESH       = 4'b0001;
  localparam CMD_LOAD_MODE     = 4'b0000;
  
  // Mode: Burst Length = 2 or 4 bytes (2x16), CAS=2
  localparam MODE_REG          = {3'b000,1'b0,2'b00,3'b010,1'b0,3'b001};
  
  // SM states
  localparam STATE_W           = 4;
  localparam STATE_INIT        = 4'd0;
  localparam STATE_DELAY       = 4'd1;
  localparam STATE_IDLE        = 4'd2;
  localparam STATE_ACTIVATE    = 4'd3;
  localparam STATE_READ        = 4'd4;
  localparam STATE_READ_WAIT   = 4'd5;
  localparam STATE_WRITE0      = 4'd6;
  localparam STATE_WRITE1      = 4'd7;
  localparam STATE_PRECHARGE   = 4'd8;
  localparam STATE_REFRESH     = 4'd9;


//ASSERTION VARIABLES
 logic cke_initialization_done,CMD_PRECHARGE_first,CMD_LOAD_MODE_first;
 logic [1:0] CMD_REFRESH_first;

 logic [3:0] command_q;
 assign command_q[3] = sdram_cs_o  ;
 assign command_q[2] = sdram_ras_o ;
 assign command_q[1] = sdram_cas_o ;
 assign command_q[0] = sdram_we_o  ;

 logic ram_req_w;
 assign ram_req_w = inport_rd_i || |inport_wr_i;

 // Address bits
 logic [SDRAM_ROW_W-1:0]  addr_col_w;
 logic [SDRAM_ROW_W-1:0]  addr_row_w;
 logic [SDRAM_BANK_W-1:0] addr_bank_w;
 
 assign addr_col_w  = {{(SDRAM_ROW_W-SDRAM_COL_W){1'b0}}, inport_addr_i[SDRAM_COL_W:2], 1'b0}; 
 assign addr_row_w  = inport_addr_i[SDRAM_ADDR_W:SDRAM_COL_W+2+1];  // 24:12 
 assign addr_bank_w = inport_addr_i[SDRAM_COL_W+2:SDRAM_COL_W+2-1]; // 11:10
 
 
  //Glue logic to check reset signals first time
	 initial
   begin
     forever
       begin
         @(posedge rst_i)
         fork
          begin
            cke_initialization_done = 0;
			      CMD_PRECHARGE_first = 0;
			      CMD_LOAD_MODE_first = 0;
			      CMD_REFRESH_first = 0;
            wait(refresh_timer_q == 50)
			@(posedge clk_i)
            cke_initialization_done = 1;
			wait(refresh_timer_q == 40)
			@(posedge clk_i)
			CMD_PRECHARGE_first = 1;
			wait(refresh_timer_q == 30);
			@(posedge clk_i)
			CMD_REFRESH_first[0] = 1;
			wait(refresh_timer_q == 20);
			@(posedge clk_i)
			CMD_REFRESH_first[1] = 1;
			wait(refresh_timer_q == 10);
			@(posedge clk_i)
			CMD_LOAD_MODE_first = 1;
          end
         join_none
       end
   end
  
  //Property for Cke_q check
  property cke_q_check_p;
    @(posedge clk_i)
    disable iff(rst_i)
    refresh_timer_q == 50 && cke_initialization_done==0 |-> $rose(sdram_cke_o) ##0 sdram_cke_o[*0:$] ;
  endproperty
  
  
  
  CKE_Q_ASSERT_CHECK_a:assert property (cke_q_check_p)
    else
      begin
        $error("CKE_Q did not assert as expected");
      end
  
  //Property for Reset check for all signals.
  property reset_check_p;
    @(posedge clk_i)
    $rose(rst_i) |=> ((command_q              == CMD_NOP                ) && 
                      (sdram_addr_o           == {SDRAM_ROW_W{1'b0}}    ) && 
                      (sdram_ba_o             == {SDRAM_BANK_W{1'b0}}   ) && 
                      (state_q                == STATE_INIT             ) && 
                      (refresh_timer_q        == SDRAM_START_DELAY + 100) );
  endproperty
  
    RESET_CHECK_a: assert property (reset_check_p)
    else
      begin
        $error("Reset signals not matching with expected values");
      end
  	
  property ack_q_check_p;
    @(posedge clk_i)
    disable iff(rst_i)
    (state_q == STATE_WRITE1) || (rd_q[SDRAM_READ_LATENCY]) |-> $rose(inport_ack_o);
  endproperty
    
      ACK_q_CHECK_a: assert property (ack_q_check_p)
    else
      begin
        $error("ACK_Q did not assert accordingly");
	   end
	  
       property CMD_RESET_check_p(value, CMD_TO_BE_SENT,command_queue);
	     @(posedge clk_i)
          (refresh_timer_q == value) && (CMD_TO_BE_SENT == 0) |-> (command_q == command_queue);
       endproperty
  
       FIRST_PRECHARGE_CHECK_a: assert property(CMD_RESET_check_p(40,CMD_PRECHARGE_first,CMD_PRECHARGE))
						 else	
							$error("CMD_PRECHARGE FIRST CHECK FAILED");
							
         FIRST_REFRESH_CHECK_30_a: assert property(CMD_RESET_check_p(30,CMD_REFRESH_first[0],CMD_REFRESH))
						  else
							$error("CMD_REFRESH first at 30 check");
   
           SECOND_REFRESH_CHECK_20_a:assert property(CMD_RESET_check_p(20,CMD_REFRESH_first[1],CMD_REFRESH))
						  else
							$error("CMD_REFRESH first at 20 check");
							
             CMD_LOAD_MODE_first_CHECK_a :assert property(CMD_RESET_check_p(10,CMD_LOAD_MODE_first,CMD_LOAD_MODE))
							  else
								$error("CMD_LOAD_MODE_first_CHECK first at 10 check");
  
  
  property ack_negative_check_p;
    @(posedge clk_i)
    disable iff(rst_i)
    $rose(inport_ack_o) |-> (state_q == STATE_WRITE1) || (rd_q[SDRAM_READ_LATENCY]);
  endproperty
    
        ACK_NEGATIVE_CHECK_a: assert property (ack_negative_check_p)
    else
      begin
        $error("ACK NEGATIVE CHECK FAILED ASSERTED AT UNEXPECTED POINT");
      end
  
  property refresh_q_check_p;
    @(posedge clk_i)
    disable iff(rst_i)
    (refresh_timer_q == '0) |=> $rose(refresh_q);
  endproperty
          
   REFRESH_Q_ASSERT_CHECK_a: assert property(refresh_q_check_p)
            			   else
                           $error("REFRESH_Q_NOT ASSERTED AS EXPECTED");
     
     
   property state_init_idle_transition_p;
     @(posedge clk_i)
     disable iff(rst_i)
     state_q == STATE_INIT && refresh_q |=> state_q==STATE_IDLE;
   endproperty
     
   
     STATE_IDLE_TRANSITION_CHECK_a:assert property(state_init_idle_transition_p)
       						     else
                              $error("STATE_IDLE_TRANSITION from INIT NOT HAPPENED");
       
    property IDLE_PRECHARGE_Transition_p;
      @(posedge clk_i)
      disable iff(rst_i)
      state_q == STATE_IDLE && refresh_q |->  if(|row_open_q)
        									   ##1 state_q == STATE_PRECHARGE
        									   else
                                                 ##1 state_q == STATE_REFRESH;
    endproperty
       
       
       STATE_IDLE_PRECHARGE_Transition_a:assert property(IDLE_PRECHARGE_Transition_p)
         else
           $error("IDLE_PRECHARGE TRANSITION FAILED");
         
    property State_IDLE_Activate_Transition_p;
      @(posedge clk_i)
      disable iff(rst_i)
      (state_q == STATE_IDLE && ram_req_w) && !row_open_q[addr_bank_w] 
      |=> state_q == STATE_ACTIVATE;
    endproperty
         
         State_IDLE_Activate_Transition_a: assert property(State_IDLE_Activate_Transition_p)
           else
             $error("STATE_ACTIVATE Transition from IDLE failed");
 initial
   begin
    forever
      begin
        @(state_q)
        case(state_q)
          STATE_PRECHARGE : begin
            @(posedge clk_i);
            assert({sdram_cs_o ,sdram_ras_o,sdram_cas_o,sdram_we_o} ==CMD_PRECHARGE);
          end
          STATE_ACTIVATE : begin
            @(posedge clk_i);
            assert({sdram_cs_o ,sdram_ras_o,sdram_cas_o,sdram_we_o} ==CMD_ACTIVE);
          end
             STATE_REFRESH : begin
               @(posedge clk_i);
               assert({sdram_cs_o ,sdram_ras_o,sdram_cas_o,sdram_we_o} ==CMD_REFRESH);
             end     
        endcase
      end
   end
 
 
 
 
endmodule