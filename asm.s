	.syntax unified
	.cpu cortex-m4
    
	.global LogTable_q3
	.global ExpTable_q3
	.set q_1, 256  
	.set q_2, 256           
	.set q_3, 512  
	.set d, 2                                         
	.set q3_to_q2, 255 
	.set int_size, 2   
	.set dim_int, 1    
	.set block_size, (d+1)*int_size          
	.set column_size, 4*(d+1)*int_size
	.set slice_size, 16*(d+1)*int_size
	.set R_num, d*d
	.set s_num, d
	.set use_rng, 1
	
	.global AES_one_round_pre
	.global AES_one_round_online
    .global AES_ten_round_pre
	.global AES_ten_round_online
	
	.global AddRoundKey_pre
	.global SubBytes_pre
	.global MixColumns_pre
		
	.global MaskedTable_pre
	
    .global S
	.global A
    .global X_address	
    .global X_k		
    .global Y_address
    .global R
    .global R_T
	.global temp
		
	.global W
	.global u
		
	.global s_address
	.global s_address_1
	.global s_address_2
	.global s_address_3
	.global s_address_4
	.global s_address_5
	.global s_address_6
	.global s_address_7
	.global s_address_8
	.global s_address_9
	.global s_address_10
	.global s_address_11
	.global s_address_12
	.global s_address_13
	.global s_address_14
	.global s_address_15
	.global s_address_16
	.global s_all
	.global s_
	.global t_address
	.global t_address_1
	.global t_address_2
	.global t_address_3
	.global t_address_4
	.global t_address_5
	.global t_address_6
	.global t_address_7
	.global t_address_8
	.global t_address_9
	.global t_address_10
	.global t_address_11
	.global t_address_12
	.global t_address_13
	.global t_address_14
	.global t_address_15
	.global t_address_16
	.global t_all
	.global t_
	.global w_address
	.global w_address_1
	.global w_address_2
	.global w_address_3
	.global w_address_4
	.global w_address_5
	.global w_address_6
	.global w_address_7
	.global w_address_8
	.global w_address_9
	.global w_address_10
	.global w_address_11
	.global w_address_12
	.global w_address_13
	.global w_address_14
	.global w_address_15
	.global w_address_16
	.global w_all
	.global sw_flag
	.global t_flag
    .global y

	.global plain
	.global cipher
	.global round_key_address
	.global round_key
	.global round_key_ori		
	.global	MixColumns_table_2
	.global	MixColumns_table_3
	.global plain_masked_1
	.global plain_masked_2
    .global plain_masked_3
    .global plain_masked_4
    .global plain_masked_5
    .global plain_masked_6
    .global plain_masked_7
    .global plain_masked_8
    .global plain_masked_9
    .global plain_masked_10
    .global plain_masked_11
    .global plain_masked_12
    .global plain_masked_13
    .global plain_masked_14
    .global plain_masked_15
    .global plain_masked_16
    		
	
////////////////////////////////////////////////////////////
	.macro mult_exp_q3 opA , opB , res , table_address
	MOV \res, #0
	ADD \opA , \opB
	LDRH \opA , [ \table_address , \opA ]
	RSB \res , \opB , #0
	ASR \res , #32 
	AND \res , \opA
	MOV \opA, #0
	MOV \opB, #0
	.endmacro
////////////////////////////////////////////////////////////
	.macro Do_LogTable_q3 opA, size, tmp1, tmp2
	LDR \tmp1 , =LogTable_q3
	.ltorg
	.set i, 0
	.rept \size
        LDRH \tmp2, [\opA, #i]
		LSL \tmp2, dim_int
		LDRH \tmp2, [\tmp1, \tmp2]
		LSL \tmp2, dim_int
		STRH \tmp2, [\opA, #i]
        .set i, i+int_size
    .endr
	.endmacro
////////////////////////////////////////////////////////////
	.macro move_to opA, opB, num, tmp
	.set i, 0
	.rept \num
        LDRH \tmp, [\opA, #i]
		STRH \tmp, [\opB, #i]
        .set i, i+int_size
    .endr
	.endmacro
////////////////////////////////////////////////////////////
	.macro Small_Field opA , res
    AND \res, \opA, q3_to_q2
	.endmacro
////////////////////////////////////////////////////////////
    .macro Matrix_Add op1, op2, op3, op9, op10, opA, res
//------------------------------------------------------
    MOV \op2, #0
	MA_condition1_\@:
	SUB \op1, \op2, d*int_size
	CBNZ \op1, MA_loop1_\@
	B MA_exit1_\@
	MA_loop1_\@:              
//------------------------------------------------
    MOV \op9, #0
    MOV \op3, #0
    MA_condition2_\@:
	SUB \op1, \op3, d*int_size
	CBNZ \op1, MA_loop2_\@
	B MA_exit2_\@
	MA_loop2_\@:             

    LDRH \op10, [\opA, \op3]
	EOR \op9, \op9, \op10

	ADD \op3, \op3, int_size
	B MA_condition2_\@
	MA_exit2_\@:
//------------------------------------------------
    STRH \op9, [\res, \op2]
	
	ADD \opA, \opA, d*int_size
	ADD \op2, \op2, int_size
	B MA_condition1_\@
	MA_exit1_\@:
//------------------------------------------------------
	.endmacro
////////////////////////////////////////////////////////////	
	.macro Vector_Add op1, op2, op10, opA, res
//------------------------------------------------------
    MOV \res, #0
	MOV \op2, #0
    VA_condition1_\@:
	SUB \op1, \op2, d*int_size
	CBNZ \op1, VA_loop1_\@
	B VA_exit1_\@
	VA_loop1_\@:              

    LDRH \op10, [\opA, \op2]
	EOR \res, \res, \op10
	
	ADD \op2, \op2, int_size
	B VA_condition1_\@
	VA_exit1_\@:
//------------------------------------------------------
	.endmacro
////////////////////////////////////////////////////////////
	.macro Matrix_Transpose op1, op2, op3, op4, op10, opR, opRT
//------------------------------------------------------
    MOV \op2, #0
    MT_condition1_\@:
	SUB \op1, \op2, d*int_size
	CBNZ \op1, MT_loop1_\@
	B MT_exit1_\@
	MT_loop1_\@:           
//------------------------------------------------
    MOV \op4, \opRT
    MOV \op3, #0
    MT_condition2_\@:
	SUB \op1, \op3, d*int_size
	CBNZ \op1, MT_loop2_\@
	B MT_exit2_\@
	MT_loop2_\@:           

    LDRH \op10, [\opR, \op3]
	STRH \op10, [\op4, \op2]

    ADD \op4, \op4, d*int_size
	ADD \op3, \op3, int_size
	B MT_condition2_\@
	MT_exit2_\@:
//------------------------------------------------
    ADD \opR, \opR, d*int_size
	ADD \op2, \op2, int_size
	B MT_condition1_\@
	MT_exit1_\@:
//------------------------------------------------------
	.endmacro
////////////////////////////////////////////////////////////
	.macro LastShare_CandS op12, op11, op10, op9, op8, op5, op4, tmp1, tmp2, tmp3, table_address

    .set i, 0
        .rept d
        
		MOV \tmp1, #0
		MOV \tmp2, #0
		MOV \tmp3, #0
		LDRH \tmp1, [\op11, #i]
		LDRH \tmp2, [\op9, #i]
		mult_exp_q3 \tmp1 ,\tmp2 ,\tmp3 ,\table_address   
		MOV \tmp1, #0
		MOV \tmp2, #0
		Small_Field \tmp3, \tmp1                  
		MOV \tmp3, #0
		LDRH \tmp2, [\op12, #i]
		EOR \tmp3, \tmp1, \tmp2
		EOR \op5, \tmp3
	
		.set i, i+int_size
	.endr
	MOV \tmp1, #0
	MOV \tmp2, #0
	MOV \tmp3, #0
	
    LSL \op8, dim_int
	LDR \op12, =t_address
	LDR \op12, [\op12]
	LDRH \op12, [\op12, \op8]   
	EOR \op5, \op12

	STRH \op5, [\op10, \op4]  

	.endmacro
////////////////////////////////////////////////////////////
	.macro SubBytes_SetParameters op12, op11, op10, tmp

	LDR \tmp, =s_address_1
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_2
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_3
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_4
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_5
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_6
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_7
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_8
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_9
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_10
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_11
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_12
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_13
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_14
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_15
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	LDR \tmp, =s_address_16
	STR \op12, [\tmp]
	ADD \op12, d*int_size
	
	LDR \tmp, =t_address_1
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_2
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_3
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_4
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_5
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_6
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_7
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_8
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_9
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_10
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_11
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_12
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_13
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_14
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_15
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	LDR \tmp, =t_address_16
	STR \op11, [\tmp]
	ADD \op11, q_1*int_size
	
	LDR \tmp, =w_address_1
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_2
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_3
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_4
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_5
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_6
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_7
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_8
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_9
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_10
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_11
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_12
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_13
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_14
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_15
	STR \op10, [\tmp]
	ADD \op10, d*int_size
	LDR \tmp, =w_address_16
	STR \op10, [\tmp]
	ADD \op10, d*int_size

	.endmacro
////////////////////////////////////////////////////////////
	.macro AddRoundKey_last op12, op11, tmp1, tmp2, tmp3

	ADD \op12, d*int_size
	
	MOV \tmp1, #0
	MOV \tmp2, #0
	MOV \tmp3, #0
	LDRH \tmp2, [\op11]
	LDRH \tmp1, [\op12]
	EOR \tmp3, \tmp1, \tmp2
	MOV \tmp1, #0
	MOV \tmp2, #0
	STRH \tmp3, [\op12]
	MOV \tmp3, #0
		
	ADD \op11, block_size 

	.endmacro
////////////////////////////////////////////////////////////
	.macro AddRoundKey_online op12, op11, tmp1, tmp2, tmp3

	LDR \op11, =round_key_address
	LDR \op11, [\op11]
	ADD \op11, d*int_size
	
	LDR \op12, =plain_masked_1
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_2
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_3
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_4
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_5
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_6
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_7
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_8
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_9
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_10
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_11
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_12
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_13
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_14
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_15
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	LDR \op12, =plain_masked_16
	AddRoundKey_last \op12, \op11, \tmp1, \tmp2, \tmp3
	
	.endmacro
////////////////////////////////////////////////////////////
	.macro SBox_SetParameters X, s, t, w, X_address, Y_address, s_address, t_address, w_address

	LDR \s, [\s]
	LDR \t, [\t]
	LDR \w, [\w]
	LDR \X_address, =X_address
	LDR \Y_address, =Y_address
	LDR \s_address, =s_address
	LDR \t_address, =t_address
	LDR \w_address, =w_address
	STR \X, [\X_address]
	STR \X, [\Y_address]
	STR \s, [\s_address]
	STR \t, [\t_address]
	STR \w, [\w_address]
	
	.endmacro
////////////////////////////////////////////////////////////
	.macro SubBytes_online op12, op11, op10, op9, op8, op7, op6, op5, op4
	
	LDR \op12, =plain_masked_1
	LDR \op11, =s_address_1
	LDR \op10, =t_address_1
	LDR \op9, =w_address_1
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_2
	LDR \op11, =s_address_2
	LDR \op10, =t_address_2
	LDR \op9, =w_address_2
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_3
	LDR \op11, =s_address_3
	LDR \op10, =t_address_3
	LDR \op9, =w_address_3
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_4
	LDR \op11, =s_address_4
	LDR \op10, =t_address_4
	LDR \op9, =w_address_4
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_5
	LDR \op11, =s_address_5
	LDR \op10, =t_address_5
	LDR \op9, =w_address_5
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_6
	LDR \op11, =s_address_6
	LDR \op10, =t_address_6
	LDR \op9, =w_address_6
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_7
	LDR \op11, =s_address_7
	LDR \op10, =t_address_7
	LDR \op9, =w_address_7
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_8
	LDR \op11, =s_address_8
	LDR \op10, =t_address_8
	LDR \op9, =w_address_8
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_9
	LDR \op11, =s_address_9
	LDR \op10, =t_address_9
	LDR \op9, =w_address_9
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_10
	LDR \op11, =s_address_10
	LDR \op10, =t_address_10
	LDR \op9, =w_address_10
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_11
	LDR \op11, =s_address_11
	LDR \op10, =t_address_11
	LDR \op9, =w_address_11
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_12
	LDR \op11, =s_address_12
	LDR \op10, =t_address_12
	LDR \op9, =w_address_12
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_13
	LDR \op11, =s_address_13
	LDR \op10, =t_address_13
	LDR \op9, =w_address_13
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_14
	LDR \op11, =s_address_14
	LDR \op10, =t_address_14
	LDR \op9, =w_address_14
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_15
	LDR \op11, =s_address_15
	LDR \op10, =t_address_15
	LDR \op9, =w_address_15
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online
	
	LDR \op12, =plain_masked_16
	LDR \op11, =s_address_16
	LDR \op10, =t_address_16
	LDR \op9, =w_address_16
	SBox_SetParameters \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4
	BL ToAdditiveShares_online

    .endmacro
////////////////////////////////////////////////////////////
	.macro MixColumns_column op12, op11, op10, op9, op8, op7, op6, op5, op4, op3, op2, op1

	MOV \op4, #0
	MOV \op5, #0
	MOV \op6, #0
	MOV \op7, #0
	.ltorg
//------------------------------------------	
    MOV \op8, #0
	LDRH \op8, [\op12, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op2, \op8]
	EOR \op7, \op7, \op8

	MOV \op8, #0
	LDRH \op8, [\op11, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op3, \op8]
	EOR \op7, \op7, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op10, \op1]
	EOR \op7, \op7, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op9, \op1]
	EOR \op7, \op7, \op8
//------------------------------------------
    MOV \op8, #0
	LDRH \op8, [\op12, \op1]
	EOR \op6, \op6, \op8

    MOV \op8, #0
	LDRH \op8, [\op11, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op2, \op8]
	EOR \op6, \op6, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op10, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op3, \op8]
	EOR \op6, \op6, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op9, \op1]
	EOR \op6, \op6, \op8
//------------------------------------------	
    MOV \op8, #0
	LDRH \op8, [\op12, \op1]
	EOR \op5, \op5, \op8

    MOV \op8, #0
	LDRH \op8, [\op11, \op1]
	EOR \op5, \op5, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op10, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op2, \op8]
	EOR \op5, \op5, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op9, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op3, \op8]
	EOR \op5, \op5, \op8
//------------------------------------------
    MOV \op8, #0
	LDRH \op8, [\op12, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op3, \op8]
	EOR \op4, \op4, \op8

    MOV \op8, #0
	LDRH \op8, [\op11, \op1]
	EOR \op4, \op4, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op10, \op1]
	EOR \op4, \op4, \op8
	
	MOV \op8, #0
	LDRH \op8, [\op9, \op1]
	LSL \op8, dim_int
	LDRH \op8, [\op2, \op8]
	EOR \op4, \op4, \op8
//------------------------------------------	
    STRH \op7, [\op12, \op1]
	STRH \op6, [\op11, \op1]
	STRH \op5, [\op10, \op1]
	STRH \op4, [\op9, \op1]
	
	.endmacro
////////////////////////////////////////////////////////////
	.macro MixColumns_online op12, op11, op10, op9, op8, op7, op6, op5, op4, op3, op2, op1

	LDR \op2 ,=MixColumns_table_2
	LDR \op3 ,=MixColumns_table_3
	MOV \op1, d*int_size

    LDR \op12, =plain_masked_1
	LDR \op11, =plain_masked_5
	LDR \op10, =plain_masked_9
	LDR \op9, =plain_masked_13
	MixColumns_column \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4, \op3, \op2, \op1
	
    LDR \op12, =plain_masked_2
	LDR \op11, =plain_masked_6
	LDR \op10, =plain_masked_10
	LDR \op9, =plain_masked_14
	MixColumns_column \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4, \op3, \op2, \op1
	
    LDR \op12, =plain_masked_3
	LDR \op11, =plain_masked_7
	LDR \op10, =plain_masked_11
	LDR \op9, =plain_masked_15
	MixColumns_column \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4, \op3, \op2, \op1
	
    LDR \op12, =plain_masked_4
	LDR \op11, =plain_masked_8
	LDR \op10, =plain_masked_12
	LDR \op9, =plain_masked_16
	MixColumns_column \op12, \op11, \op10, \op9, \op8, \op7, \op6, \op5, \op4, \op3, \op2, \op1

	.endmacro
////////////////////////////////////////////////////////////	
	.macro ShiftRows_pre op_A, op_B, op_C, op_D, tmp, tmp2
	
	LDR \op_D , =plain_masked_8
	LDR \op_C , =plain_masked_7
	LDR \op_B , =plain_masked_6
	LDR \op_A , =plain_masked_5
    .set i, 0
	.rept d
	LDRH \tmp2, [\op_A, #i]
	LDRH \tmp, [\op_B, #i]
	STRH \tmp, [\op_A, #i]
	LDRH \tmp, [\op_C, #i]
	STRH \tmp, [\op_B, #i]
	LDRH \tmp, [\op_D, #i]
	STRH \tmp, [\op_C, #i]
	STRH \tmp2, [\op_D, #i]
	.set i, i+int_size
	.endr
	
	LDR \op_D , =plain_masked_12
	LDR \op_C , =plain_masked_11
	LDR \op_B , =plain_masked_10
	LDR \op_A , =plain_masked_9
    .set i, 0
	.rept d
	LDRH \tmp2, [\op_A, #i]
	LDRH \tmp, [\op_C, #i]
	STRH \tmp, [\op_A, #i]
	STRH \tmp2, [\op_C, #i]
	LDRH \tmp2, [\op_B, #i]
	LDRH \tmp, [\op_D, #i]
	STRH \tmp, [\op_B, #i]
	STRH \tmp2, [\op_D, #i]
	.set i, i+int_size
	.endr
	
	LDR \op_D , =plain_masked_16
	LDR \op_C , =plain_masked_15
	LDR \op_B , =plain_masked_14
	LDR \op_A , =plain_masked_13
    .set i, 0
	.rept d
	LDRH \tmp2, [\op_A, #i]
	LDRH \tmp, [\op_D, #i]
	STRH \tmp, [\op_A, #i]
	LDRH \tmp, [\op_C, #i]
	STRH \tmp, [\op_D, #i]
	LDRH \tmp, [\op_B, #i]
	STRH \tmp, [\op_C, #i]
	STRH \tmp2, [\op_B, #i]
	.set i, i+int_size
	.endr

	.endm
////////////////////////////////////////////////////////////	
	.macro ShiftRows_online op_A, op_B, op_C, op_D, tmp, tmp2
	
	.set i, d*int_size
	
	LDR \op_D , =plain_masked_8
	LDR \op_C , =plain_masked_7
	LDR \op_B , =plain_masked_6
	LDR \op_A , =plain_masked_5
	LDRH \tmp2, [\op_A, #i]
	LDRH \tmp, [\op_B, #i]
	STRH \tmp, [\op_A, #i]
	MOV \tmp, #0
	LDRH \tmp, [\op_C, #i]
	STRH \tmp, [\op_B, #i]
	MOV \tmp, #0
	LDRH \tmp, [\op_D, #i]
	STRH \tmp, [\op_C, #i]
	MOV \tmp, #0
	STRH \tmp2, [\op_D, #i]
	
	LDR \op_D , =plain_masked_12
	LDR \op_C , =plain_masked_11
	LDR \op_B , =plain_masked_10
	LDR \op_A , =plain_masked_9
	LDRH \tmp2, [\op_A, #i]
	LDRH \tmp, [\op_C, #i]
	STRH \tmp, [\op_A, #i]
	MOV \tmp, #0
	STRH \tmp2, [\op_C, #i]
	LDRH \tmp2, [\op_B, #i]
	MOV \tmp, #0
	LDRH \tmp, [\op_D, #i]
	STRH \tmp, [\op_B, #i]
	MOV \tmp, #0
	STRH \tmp2, [\op_D, #i]
	
	LDR \op_D , =plain_masked_16
	LDR \op_C , =plain_masked_15
	LDR \op_B , =plain_masked_14
	LDR \op_A , =plain_masked_13
	LDRH \tmp2, [\op_A, #i]
	LDRH \tmp, [\op_D, #i]
	STRH \tmp, [\op_A, #i]
	MOV \tmp, #0
	LDRH \tmp, [\op_C, #i]
	STRH \tmp, [\op_D, #i]
	MOV \tmp, #0
	LDRH \tmp, [\op_B, #i]
	STRH \tmp, [\op_C, #i]
	MOV \tmp, #0
	STRH \tmp2, [\op_B, #i]

	.endm
////////////////////////////////////////////////////////////--------------

////////////////////////////////////////////////////////////--------------
	Gennerate_plain_masked:
	LDRH r9, [r10]
//------------------------------------------------	
	MOV r1, #0
    AORP_condition1:
	SUB r6, r1, d*int_size
	CBNZ r6, AORP_loop1
	B AORP_exit1
	AORP_loop1:         
	
	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	MOV r2, r0
	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	EOR r0, r1
	AND r0, #0xff	

	EOR r9, r0
	STRH r0, [r12, r1]
	
	ADD r1, r1, int_size
	B AORP_condition1
	AORP_exit1:
//------------------------------------------------	
    STRH r9, [r12, r1]
    ADD r10, int_size
	
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
	Gennerate_roundkey_masked:
	LDR r12, =round_key
	LDR r11, =round_key_ori
//------------------------------------------------------	
	MOV r1, #0
    GRKM_condition1:
	SUB r2, r1, 16*int_size
	CBNZ r2, GRKM_loop1
	B GRKM_exit1
	GRKM_loop1: 
	
	LDRH r6, [r11, r1]
	MOV r0, d+1
	MUL r5, r1, r0
//------------------------------------------------	
	MOV r3, #0
    GRKM_condition2:
	SUB r4, r3, d*int_size
	CBNZ r4, GRKM_loop2
	B GRKM_exit2
	GRKM_loop2:       

	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	MOV r8, r0
	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	EOR r0, r1
	AND r0, #0xff	
		
	ADD r7, r5, r3
    STRH r0, [r12, r7]
	EOR r6, r0
	
	ADD r3, r3, int_size
	B GRKM_condition2
	GRKM_exit2:
//------------------------------------------------
	ADD r5, r3
    STRH r6, [r12, r5]

	ADD r1, r1, int_size
	B GRKM_condition1
	GRKM_exit1:
//------------------------------------------------------
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
    AES_one_round_pre:
	PUSH {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	
	LDR r12, =s_all
	LDR r11, =t_all
	LDR r10, =w_all
	LDR r9, =sw_flag
	LDR r8, =t_flag
	LDRH r7, [r9]
	LDR r6, [r8]
	ADD r12, r7
	ADD r11, r6
	ADD r10, r7
	ADD r7, 16*d*int_size
	ADD r6, 16*q_1*int_size
	STRH r7, [r9]
	STR r6, [r8]
	
	SubBytes_SetParameters r12, r11, r10, r9
	BL SubBytes_pre
	ShiftRows_pre r5, r4, r3, r2, r1, r0
	BL MixColumns_pre

	POP {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
	AES_one_round_online:
	PUSH {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	
	LDR r12, =s_all
	LDR r11, =t_all
	LDR r10, =w_all
	LDR r9, =sw_flag
	LDR r8, =t_flag
	LDRH r7, [r9]
	LDR r6, [r8]
	ADD r12, r7
	ADD r11, r6
	ADD r10, r7
	ADD r7, 16*d*int_size
	ADD r6, 16*q_1*int_size
	STRH r7, [r9]
	STR r6, [r8]
	MOV r6, #0
	MOV r7, #0
	MOV r8, #0
	SubBytes_SetParameters r12, r11, r10, r9
	MOV r9, #0
	MOV r10, #0
	MOV r11, #0
	MOV r12, #0
	SubBytes_online r12, r11, r10, r9, r8, r7, r6, r5, r4
	MOV r4, #0
	MOV r5, #0
	MOV r6, #0
	MOV r7, #0
	MOV r8, #0
	MOV r9, #0
	MOV r10, #0
	MOV r11, #0
	MOV r12, #0
	ShiftRows_online r5, r4, r3, r2, r1, r0
	MOV r0, #0
	MOV r1, #0
	MOV r2, #0
	MOV r3, #0
	MOV r4, #0
	MOV r5, #0
	MixColumns_online r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1
	MOV r1, #0
	MOV r2, #0
	MOV r3, #0
	MOV r4, #0
	MOV r5, #0
	MOV r6, #0
	MOV r7, #0
	MOV r8, #0
	MOV r9, #0
	MOV r10, #0
	MOV r11, #0
	MOV r12, #0
	
	POP {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
    AES_ten_round_pre:
	PUSH {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	.ltorg
	
	BL Gennerate_roundkey_masked
	
	LDR r10, =plain	
    LDR r12, =plain_masked_1
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_2
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_3
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_4
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_5
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_6
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_7
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_8
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_9
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_10
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_11
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_12
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_13
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_14
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_15
	BL Gennerate_plain_masked
	LDR r12, =plain_masked_16
	BL Gennerate_plain_masked

//=========================================== initial round	
	LDR r12, =round_key_address
	LDR r11, =round_key
	STR r11, [r12]
	BL AddRoundKey_pre
//=========================================== 9 round
	MOV r1, #0
    ATRP_condition1:
	SUB r0, r1, #9
	CBNZ r0, ATRP_loop1
	B ATRP_exit1
	ATRP_loop1:            

	BL AES_one_round_pre

	ADD r1, r1, #1
	B ATRP_condition1
	ATRP_exit1:
//=========================================== final round	
	LDR r12, =s_all
	LDR r11, =t_all
	LDR r10, =w_all
	LDR r9, =sw_flag
	LDR r8, =t_flag
	LDRH r7, [r9]
	LDR r6, [r8]
	ADD r12, r7
	ADD r11, r6
	ADD r10, r7
	ADD r7, 16*d*int_size
	ADD r6, 16*q_1*int_size
	STRH r7, [r9]
	STR r6, [r8]
	SubBytes_SetParameters r12, r11, r10, r9
	BL SubBytes_pre
	ShiftRows_pre r5, r4, r3, r2, r1, r0

	POP {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
	AES_ten_round_online:
	PUSH {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	.ltorg
	LDR r12, =sw_flag
	LDR r11, =t_flag
	LDRH r10, [r12]
	LDR r9, [r11]
	MOV r10, #0
	MOV r9, #0
	STRH r10, [r12]
	STR r9, [r11]
//=========================================== initial round		
	LDR r12, =round_key_address
	LDR r11, =round_key
	STR r11, [r12]
	AddRoundKey_online r12, r11, r10, r9, r8
	MOV r8, #0
	MOV r9,  #0
	MOV r10, #0
	MOV r11, #0
	MOV r12, #0
//=========================================== 9 round	
	MOV r1, #0
    ATRO_condition1:
	SUB r0, r1, #9
	CBNZ r0, ATRO_loop1
	B ATRO_exit1
	ATRO_loop1:  

	BL AES_one_round_online

	ADD r1, r1, #1
	B ATRO_condition1
	ATRO_exit1:
//=========================================== final round
	LDR r12, =s_all
	LDR r11, =t_all
	LDR r10, =w_all
	LDR r9, =sw_flag
	LDR r8, =t_flag
	LDRH r7, [r9]
	LDR r6, [r8]
	ADD r12, r7
	ADD r11, r6
	ADD r10, r7
	ADD r7, 16*d*int_size
	ADD r6, 16*q_1*int_size
	STRH r7, [r9]
	STR r6, [r8]
	MOV r6, #0
	MOV r7, #0
	MOV r8, #0
	MOV r9, #0
	SubBytes_SetParameters r12, r11, r10, r9
	MOV r9, #0
	MOV r10, #0
	MOV r11, #0
	MOV r12, #0
	SubBytes_online r12, r11, r10, r9, r8, r7, r6, r5, r4
	MOV r4, #0
	MOV r5, #0
	MOV r6, #0
	MOV r7, #0
	MOV r8, #0
	MOV r9, #0
	MOV r10, #0
	MOV r11, #0
	MOV r12, #0
	ShiftRows_online r5, r4, r3, r2, r1, r0
	MOV r0, #0
	MOV r1, #0
	MOV r2, #0
	MOV r3, #0
	MOV r4, #0
	MOV r5, #0

	POP {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
	AddRoundKey_block:
//------------------------------------------------------
	MOV r1, #0
    ARKB_condition1:
	SUB r0, r1, d*int_size
	CBNZ r0, ARKB_loop1
	B ARKB_exit1
	ARKB_loop1:          
	
	LDRH r10, [r12, r1]
	LDRH r9, [r11, r1]
	EOR r10, r10, r9
	STRH r10, [r12, r1]
	
	ADD r1, r1, int_size
	B ARKB_condition1
	ARKB_exit1:
//------------------------------------------------------
	ADD r11, block_size     
	
	BX lr
////////////////////////////////////////////////////////////
	AddRoundKey_pre:
	PUSH {lr}
	
	LDR r11, =round_key_address
	LDR r11, [r11]
	LDR r12, =plain_masked_1
	BL AddRoundKey_block
	LDR r12, =plain_masked_2
	BL AddRoundKey_block
	LDR r12, =plain_masked_3
	BL AddRoundKey_block
	LDR r12, =plain_masked_4
	BL AddRoundKey_block
	LDR r12, =plain_masked_5
	BL AddRoundKey_block
	LDR r12, =plain_masked_6
	BL AddRoundKey_block
	LDR r12, =plain_masked_7
	BL AddRoundKey_block
	LDR r12, =plain_masked_8
	BL AddRoundKey_block
	LDR r12, =plain_masked_9
	BL AddRoundKey_block
	LDR r12, =plain_masked_10
	BL AddRoundKey_block
	LDR r12, =plain_masked_11
	BL AddRoundKey_block
	LDR r12, =plain_masked_12
	BL AddRoundKey_block	 
	LDR r12, =plain_masked_13
	BL AddRoundKey_block
	LDR r12, =plain_masked_14
	BL AddRoundKey_block
	LDR r12, =plain_masked_15
	BL AddRoundKey_block
	LDR r12, =plain_masked_16
	BL AddRoundKey_block

    POP {lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
	SBox_SetParameters:

	LDR r11, [r11]
	LDR r10, [r10]
	LDR r9, [r9]
	LDR r8, =X_address
	LDR r7, =Y_address
	LDR r6, =s_address
	LDR r5, =t_address
	LDR r4, =w_address
	STR r12, [r8]
	STR r12, [r7]
	STR r11, [r6]
	STR r10, [r5]
	STR r9, [r4]

    BX lr
////////////////////////////////////////////////////////////
	SubBytes_pre:
	PUSH {lr}

	LDR r12, =plain_masked_1
	LDR r11, =s_address_1
	LDR r10, =t_address_1
	LDR r9, =w_address_1
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_2
	LDR r11, =s_address_2
	LDR r10, =t_address_2
	LDR r9, =w_address_2
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_3
	LDR r11, =s_address_3
	LDR r10, =t_address_3
	LDR r9, =w_address_3
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_4
	LDR r11, =s_address_4
	LDR r10, =t_address_4
	LDR r9, =w_address_4
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_5
	LDR r11, =s_address_5
	LDR r10, =t_address_5
	LDR r9, =w_address_5
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_6
	LDR r11, =s_address_6
	LDR r10, =t_address_6
	LDR r9, =w_address_6
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_7
	LDR r11, =s_address_7
	LDR r10, =t_address_7
	LDR r9, =w_address_7
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_8
	LDR r11, =s_address_8
	LDR r10, =t_address_8
	LDR r9, =w_address_8
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_9
	LDR r11, =s_address_9
	LDR r10, =t_address_9
	LDR r9, =w_address_9
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_10
	LDR r11, =s_address_10
	LDR r10, =t_address_10
	LDR r9, =w_address_10
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_11
	LDR r11, =s_address_11
	LDR r10, =t_address_11
	LDR r9, =w_address_11
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_12
	LDR r11, =s_address_12
	LDR r10, =t_address_12
	LDR r9, =w_address_12
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_13
	LDR r11, =s_address_13
	LDR r10, =t_address_13
	LDR r9, =w_address_13
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_14
	LDR r11, =s_address_14
	LDR r10, =t_address_14
	LDR r9, =w_address_14
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_15
	LDR r11, =s_address_15
	LDR r10, =t_address_15
	LDR r9, =w_address_15
	BL SBox_SetParameters
	BL MaskedTable_pre
	
	LDR r12, =plain_masked_16
	LDR r11, =s_address_16
	LDR r10, =t_address_16
	LDR r9, =w_address_16
	BL SBox_SetParameters
	BL MaskedTable_pre

    POP {lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
	MixColumns_pre:
	PUSH {lr}
	
	LDR r2 ,=MixColumns_table_2
	LDR r3 ,=MixColumns_table_3
//------------------------------------------------
	MOV r1, #0
    MCP_condition1:
	SUB r0, r1, d*int_size
	CBNZ r0, MCP_loop1
	B MCP_exit1
	MCP_loop1:           

    LDR r12, =plain_masked_1
	LDR r11, =plain_masked_5
	LDR r10, =plain_masked_9
	LDR r9, =plain_masked_13
	MixColumns_column r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1
	
    LDR r12, =plain_masked_2
	LDR r11, =plain_masked_6
	LDR r10, =plain_masked_10
	LDR r9, =plain_masked_14
	MixColumns_column r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1
	
    LDR r12, =plain_masked_3
	LDR r11, =plain_masked_7
	LDR r10, =plain_masked_11
	LDR r9, =plain_masked_15
	MixColumns_column r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1
	
    LDR r12, =plain_masked_4
	LDR r11, =plain_masked_8
	LDR r10, =plain_masked_12
	LDR r9, =plain_masked_16
	MixColumns_column r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1

	ADD r1, r1, int_size
	B MCP_condition1
	MCP_exit1:
//------------------------------------------------	
    POP {lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
    MaskedTable_pre:
	PUSH {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	
	LDR r12, =S
	LDR r11, =t_address
	LDR r11, [r11]
//------------------------------------------------------	
	MOV r1, #0
    MTP_condition1:
	SUB r0, r1, q_1*int_size
	CBNZ r0, MTP_loop1
	B MTP_exit1
	MTP_loop1:             

    LDRH r10, [r12, r1]
	STRH r10, [r11, r1]

	ADD r1, r1, int_size
	B MTP_condition1
	MTP_exit1:
//------------------------------------------------------	
//------------------------------------------------------	
	MOV r1, #0
    MTP_condition2:
	SUB r0, r1, d*int_size
	CBNZ r0, MTP_loop2
	B MTP_exit2
	MTP_loop2:          
	PUSH {r1}

	LDR r2, =X_address
	LDR r2, [r2]
	LDRH r2, [r2, r1]
	LDR r3, =X_k
	STR r2, [r3]
    BL PackedShiftRefresh   
	
	POP {r1}
	ADD r1, r1, int_size
	B MTP_condition2
	MTP_exit2:
//------------------------------------------------------
    LDR r9, =s_address
	LDR r9, [r9]
	Do_LogTable_q3 r9, s_num, r0, r1

    BL ToAdditiveShares_pre

	POP {r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
    PackedShiftRefresh:    
	LDR r12, =R
//------------------------------------------------------	
	MOV r1, #0
    PSR_condition1:
	SUB r6, r1, d*d*int_size
	CBNZ r6, PSR_loop1
	B PSR_exit1
	PSR_loop1:             

	.if use_rng == 1
	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	MOV r2, r0
	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	EOR r0, r1
	AND r0, #0xff	
	.else
	MOV r0, #0
	.endif
	STRH r0, [r12, r1]
	
	ADD r1, r1, int_size
	B PSR_condition1
	PSR_exit1:
//------------------------------------------------------
	LDR r11, =s_
	Matrix_Add  r0, r1, r2, r3, r4, r12, r11 
	
    LDR r11, =R_T
	Matrix_Transpose r0, r1, r2, r3, r4, r12, r11
	
	LDR r12, =R
	Do_LogTable_q3 r12, R_num, r1, r2
	
	LDR r11, =A
	LDR r10, =W
	LDR r8, =ExpTable_q3
//------------------------------------------------------	
	MOV r1, #0
    PSR_condition2:
	SUB r0, r1, q_1
	CBNZ r0, PSR_loop2
	B PSR_exit2
	PSR_loop2:              
//------------------------------------------------
    MOV r2, #0
    PSR_condition3:
	SUB r0, r2, d*int_size
	CBNZ r0, PSR_loop3
	B PSR_exit3
	PSR_loop3:            
//------------------------------------------
    MOV r3, #0
	MOV r9, #0
	MOV r0, d*int_size
	MUL r4, r1, r0
	ADD r4, r11, r4
	ADD r5, r12, r2

    PSR_condition4:
	SUB r0, r3, d
	CBNZ r0, PSR_loop4
	B PSR_exit4
	PSR_loop4:              
	
	LDRH r6, [r4]
	LDRH r7, [r5]
	mult_exp_q3 r6, r7, r0, r8
	
	EOR r9, r0
	
	ADD r4, r4, int_size
	ADD r5, r5, d*int_size
	ADD r3, r3, 1
	B PSR_condition4
	PSR_exit4:
//------------------------------------------
	MOV r0, d*int_size
	MUL r4, r1, r0
	ADD r4, r4, r2
	STRH r9, [r10, r4]       
	
	ADD r2, r2, int_size
	B PSR_condition3
	PSR_exit3:
//------------------------------------------------
	ADD r1, r1, 1
	B PSR_condition2
	PSR_exit2:
//------------------------------------------------------

	LDR r10, =t_address
	LDR r10, [r10]
	LDR r9, =t_
    move_to r10, r9, q_1, r0  

    LDR r2, =X_k    
	LDRH r2, [r2]
	LSL r2, r2, dim_int    
	LDR r10, =W
	LDR r9, =A
	LDR r6, =u
	LDR r7, =s_address
	LDR r7, [r7]
	Do_LogTable_q3 r7, s_num, r0, r1
	LDR r8, =ExpTable_q3
//------------------------------------------------------	
    MOV r1, #0
    PSR_condition5:
	SUB r0, r1, q_1*int_size
	CBNZ r0, PSR_loop5
	B PSR_exit5
	PSR_loop5:              
	
	EOR r4, r2, r1 
	MOV r0, d
	MUL r4, r0
	MUL r3, r1, r0
//------------------------------------------------	
	MOV r5, #0
    PSR_condition6:
	SUB r0, r5, d*int_size
	CBNZ r0, PSR_loop6
	B PSR_exit6
	PSR_loop6:              
	
	ADD r0, r4, r5
	LDRH r11, [r9, r0]    
	LDRH r12, [r7, r5]    
	mult_exp_q3 r11 ,r12 ,r0 ,r8

	ADD r12, r3, r5
	LDRH r12, [r10, r12]
	EOR r0, r12
	STRH r0, [r6, r5]
	
	ADD r5, r5, int_size
	B PSR_condition6
	PSR_exit6:
//------------------------------------------------ 
	LDR r10, =t_address
	LDR r10, [r10]
	LDR r9, =t_
	Vector_Add r0, r11, r12, r6, r5 
	Small_Field r5, r5              
	EOR r4, r2, r1 
	LDRH r4, [r9, r4]
	EOR r5, r5, r4
    STRH r5, [r10, r1]

	LDR r10, =W
	LDR r9, =A

	ADD r1, r1, int_size
	B PSR_condition5
	PSR_exit5:
//------------------------------------------------------
	LDR r11, =s_address
	LDR r11, [r11]
	LDR r12, =s_
    move_to r12, r11, d, r0    
	
    BX lr
////////////////////////////////////////////////////////////
	
////////////////////////////////////////////////////////////
	ToAdditiveShares_pre:
	
	LDR r12, =R
//------------------------------------------------------	
	MOV r6, #0
    TASP_condition1:
	SUB r1, r6, d*d*int_size
	CBNZ r1, TASP_loop1
	B TASP_exit1
	TASP_loop1:              

	.if use_rng == 1
	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	MOV r2, r0
	PUSH{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BL rand  
	POP{r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	EOR r0, r1
	AND r0, #0xff	
	.else
	MOV r0, #0
	.endif
	STRH r0, [r12, r6]
	
	ADD r6, r6, int_size
	B TASP_condition1
	TASP_exit1:
//------------------------------------------------------
    LDR r11, =R_T
	LDR r12, =R
	Matrix_Transpose r0, r1, r2, r3, r4, r12, r11     
	LDR r11, =R_T
	LDR r10, =Y_address
	LDR r10, [r10]
	Matrix_Add r0, r1, r2, r3, r4, r11, r10       

	LDR r9, =w_address
	LDR r9, [r9]
	LDR r12, =R
	Matrix_Add r0, r1, r2, r3, r4, r12, r9      

	BX lr
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
    ToAdditiveShares_online:
	PUSH {r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}

	LDR r12, =X_address
	LDR r12, [r12]
	MOV r4, #1  
	MOV r0, d*int_size
	MUL r4, r0
	LDRH r8, [r12, r4]  
	MUL r9, r8, r0
	LDR r11, =A
	ADD r11, r9
	LDR r10, =Y_address
	LDR r10, [r10]
	LDR r9, =s_address
	LDR r9, [r9]
	
	LDR r12, =w_address
	LDR r12, [r12]
	LDR r3, =ExpTable_q3
	MOV r5, #0    
	MOV r0, #0
	MOV r1, #0
	MOV r2, #0
	
	LastShare_CandS r12, r11, r10, r9, r8, r5, r4, r0, r1, r2, r3

	MOV r0, #0
	MOV r1, #0
	MOV r2, #0
	MOV r3, #0
	MOV r4, #0
	MOV r5, #0
	MOV r6, #0
	MOV r7, #0
	MOV r8, #0
	MOV r9, #0
	MOV r10, #0
	MOV r11, #0
	MOV r12, #0
	
	POP {r4,r5,r6,r7,r8,r9,r10,r11,r12,lr}
	BX lr
////////////////////////////////////////////////////////////
	
.end