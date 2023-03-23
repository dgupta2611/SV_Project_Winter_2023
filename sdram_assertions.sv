module sdram_assertions();
//ASSERTION VARIABLES
 logic cke_initialization_done,CMD_PRECHARGE_first,CMD_LOAD_MODE_first;
 logic [1:0] CMD_REFRESH_first;
 
 
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
  property cke_q_check;
    @(posedge rst_i)
    disable iff(rst_i)
    refresh_timer_q == 50 && cke_initialization_done==0 |=> $rose(cke_q) ##0 cke_q[*0:$] ;
  endproperty
  
  
  
  CKE_Q_ASSERT_CHECK:assert property (cke_q_check)
    else
      begin
        $error("CKE_Q did not assert as expected");
      end
  
  //Property for Reset check for all signals.
  property reset_check;
    @(posedge clk_i)
    $rose(rst_i) |=>     command_q == CMD_NOP && data_q == 16'b0 &&addr_q          == {SDRAM_ROW_W{1'b0}} && bank_q          == {SDRAM_BANK_W{1'b0}} && cke_q           == 1'b0 && dqm_q           =={SDRAM_DQM_W{1'b0}} && data_rd_en_q    == 1'b1 && dqm_buffer_q    == {SDRAM_DQM_W{1'b0}} && state_q==STATE_INIT && refresh_timer_q == SDRAM_START_DELAY + 100;
  endproperty
  
    RESET_CHECK: assert property (reset_check)
    else
      begin
        $error("Reset signals not matching with expected values");
      end
  	
  property ack_q_check;
    @(posedge clk_i)
    disable iff(rst_i)
    state_q == STATE_WRITE1 || rd_q[SDRAM_READ_LATENCY+1] |=> $rose(ack_q);
  endproperty
    
      ACK_q_CHECK: assert property (ack_q_check)
    else
      begin
        $error("ACK_Q did not assert accordingly");
	   end
	  
        property CMD_RESET_check(value, CMD_TO_BE_SENT,command_queue);
	@(posedge clk_i)
          refresh_timer_q == value && CMD_TO_BE_SENT == 0 |=> (command_q == command_queue,$display(command_q,command_queue));
  endproperty
  
       FIRST_PRECHARGE_CHECK: assert property(CMD_RESET_check(40,CMD_PRECHARGE_first,CMD_PRECHARGE))
						 else	
							$error("CMD_PRECHARGE FIRST CHECK FAILED");
							
         FIRST_REFRESH_CHECK_30: assert property(CMD_RESET_check(30,CMD_REFRESH_first[0],CMD_REFRESH))
						  else
							$error("CMD_REFRESH first at 30 check");
   
           SECOND_REFRESH_CHECK_20:assert property(CMD_RESET_check(20,CMD_REFRESH_first[1],CMD_REFRESH))
						  else
							$error("CMD_REFRESH first at 20 check");
							
             CMD_LOAD_MODE_first_CHECK :assert property(CMD_RESET_check(10,CMD_LOAD_MODE_first,CMD_LOAD_MODE))
							  else
								$error("CMD_LOAD_MODE_first_CHECK first at 10 check");
  
  
  property ack_negative_check;
    @(posedge clk_i)
    disable iff(rst_i)
    $rose(ack_q) |-> $past(state_q) == STATE_WRITE1 || $past(rd_q[SDRAM_READ_LATENCY+1]);
  endproperty
    
        ACK_NEGATIVE_CHECK: assert property (ack_negative_check)
    else
      begin
        $error("ACK NEGATIVE CHECK FAILED ASSERTED AT UNEXPECTED POINT");
      end
  
  property refresh_q_check;
    @(posedge clk_i)
    disable iff(rst_i)
    refresh_timer_q == {REFRESH_CNT_W{1'b0}} |=> $rose(refresh_q) ##1 $fell(refresh_q);
  endproperty
          
   REFRESH_Q_ASSERT_CHECK: assert property(refresh_q_check)
            			   else
                           $error("REFRESH_Q_NOT ASSERTED AS EXPECTED");
     
     
   property state_init_idle_transition;
     @(posedge clk_i)
     disable iff(rst_i)
     state_q == STATE_INIT && refresh_q |=> state_q==STATE_IDLE;
   endproperty
     
   
     STATE_IDLE_TRANSITION_CHECK:assert property(state_init_idle_transition)
       						     else
                              $error("STATE_IDLE_TRANSITION from INIT NOT HAPPENED");
       
    property IDLE_PRECHARGE_Transition;
      @(posedge clk_i)
      disable iff(rst_i)
      state_q == STATE_IDLE && refresh_q |->  if(|row_open_q)
        									   ##1 state_q == STATE_PRECHARGE
        									   else
                                                 ##1 state_q == STATE_REFRESH;
    endproperty
       
       
       STATE_IDLE_PRECHARGE_Transition:assert property(IDLE_PRECHARGE_Transition)
         else
           $error("IDLE_PRECHARGE TRANSITION FAILED");
         
    property State_IDLE_Activate_Transition;
      @(posedge clk_i)
      disable iff(rst_i)
      (state_q == STATE_IDLE && ram_req_w) ##0 !((row_open_q[addr_bank_w] && addr_row_w == active_row_q[addr_bank_w]) && row_open_q[addr_bank_w]) 
      |=> state_q == STATE_ACTIVATE;
    endproperty
         
         assert property(State_IDLE_Activate_Transition)
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