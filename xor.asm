.model large
.stack 20h
.data
vars_start LABEL byte
	intro_msg db "[[ XOR <=512B-keys File Encryption & Decryption Program ]]$"
	info_msg db "[[ File names have to be less than 13 characters, including extension ]]$"
	data_msg db "--> Data file name: $"
	key_msg db "--> Key file name: $"
	res_msg db "--> Result file name: $"
	err_msg db "[[ ERR: $"
	err_end_msg db " is missing! ]]$"
	err_open_msg db "[[ ERR: Could not open a file! ]]$"
	err_create_msg db "[[ ERR: Could not create the result file! ]]$"
	success_msg db "[[ DONE! ]]$"
	
	data_buf db 13, 0, 13 dup(0)
	key_buf db 13, 0, 13 dup(0)
	res_buf db 13, 0, 13 dup(0)
	
	data db 13 dup (0)
	key db 13 dup (0)
	res db 13 dup (0)
	
	data_handle dw ?
	key_handle dw ?
	res_handle dw ?
	
	data_content db 512 dup (0)
	key_content db 512 dup (0)
	res_content db 512 dup (0)
	
	key_len dw 0
	bytes_read dw 0
vars_end LABEL byte
vars_size EQU vars_end - vars_start
.code
start:
	_START MACRO
		mov AX, @data
		mov DS, AX
	ENDM

	_EXIT_DOS MACRO
		mov AX, 4C00h
		int 21h
	ENDM
	
	_NEWLINE MACRO
		push AX
		push DX
		
		mov AH, 02h
		mov DL, 0Dh
		int 21h
		mov DL, 0Ah
		int 21h
		
		pop DX
		pop AX
	ENDM

	_SPRINTF MACRO src
		push DX
		push AX
	
		mov DX, offset src
		mov AH, 09h
		int 21h
		
		pop AX
		pop DX
	ENDM
	
	_NSPRINTF MACRO src
		_SPRINTF src
		_NEWLINE
	ENDM
	
	_SSCANF MACRO dst
		push DX
		push AX
		
		mov DX, offset dst
		mov AH, 0Ah
		int 21h
		
		pop AX
		pop DX
	ENDM
	
	_BUF_STRCPY MACRO dst, src
		push CX
		push SI
		push DI
		push ES
		push AX
		
		mov AX, DS
		mov ES, AX
		
		mov SI, offset src
		xor CH, CH
		mov CL, byte ptr DS:[SI+1]
		add SI, 2
		mov DI, offset dst
		rep movsb
		
		mov byte ptr [DI], 0
		
		pop AX
		pop ES
		pop DI
		pop SI
		pop CX
	ENDM
	
	_FILE_NOT_FOUND MACRO filename
		_SPRINTF err_msg
		_SPRINTF filename
		_NSPRINTF err_end_msg
	ENDM
	
	_FIND_FILE MACRO filename
		local found, not_found
		push AX
		push DX
		
		mov AH, 11h
		mov DX, offset filename
		int 21h
		
		jc not_found
		jmp found
		
		not_found:
			_FILE_NOT_FOUND filename
			_EXIT_DOS
			
		found:
			pop DX
			pop AX
	ENDM
	
	_OPEN_FILE MACRO filename, handle, mode, err
		local open_failed, open_ok
		push AX
		push DX
		
		mov AH, 3Dh
		mov AL, mode ;0=read, 1=write, 2=read/write
		mov DX, offset filename
		int 21h
		
		jc open_failed
		mov handle, AX
		
		pop DX
		pop AX
		
		jmp open_ok
		
		open_failed:
			_NEWLINE
			_NSPRINTF err
			_EXIT_DOS
			
		open_ok:
	ENDM
	
	_CLOSE_FILE MACRO handle
		push AX
		push BX
		
		mov AH, 3Eh
		mov BX, handle
		int 21h
		
		pop BX
		pop AX
	ENDM
	
	_CREATE_FILE MACRO filename, err
		local created, not_created
		push AX
		push CX
		push DX
		
		mov AH, 3Ch
		xor CX, CX
		mov DX, offset filename
		int 21h
		
		jc not_created
		jmp created
		
		not_created:
			_NEWLINE
			_NSPRINTF err
			_EXIT_DOS
		
		created:
			pop DX
			pop CX
			pop AX
	ENDM
	
	_CLEAN MACRO
		local erase
		xor BX, BX
		xor CX, CX
		xor DX, DX
		
		lea SI, vars_start
		mov CX, vars_size
		xor AX, AX
		erase:
			mov byte ptr DS:[SI], AL
			inc SI
			loop erase
	ENDM
	
	Main PROC NEAR
		_START
	
		_NEWLINE
		_NSPRINTF intro_msg
		_NSPRINTF info_msg
		
		_NEWLINE
		_SPRINTF data_msg
		_SSCANF data_buf
		_NEWLINE
		_SPRINTF key_msg
		_SSCANF key_buf
		_NEWLINE
		_SPRINTF res_msg
		_SSCANF res_buf
		_NEWLINE
		_NEWLINE
		
		_BUF_STRCPY data, data_buf
		_BUF_STRCPY key, key_buf
		_BUF_STRCPY res, res_buf
		
		_FIND_FILE data
		_FIND_FILE key
		
		_OPEN_FILE data, data_handle, 0, err_open_msg
		_OPEN_FILE key, key_handle, 0, err_open_msg
		_CREATE_FILE res, err_create_msg
		_OPEN_FILE res, res_handle, 1, err_open_msg
		
	;----------------------------------------------
    ; XOR encrypt/decrypt data with key (streaming)
    ;----------------------------------------------

    ;read KEY (<=512 bytes) into key_content
    mov bx, key_handle
    mov dx, OFFSET key_content
    mov cx, 512
    call ReadFile
    jc key_read_err
    mov [key_len], ax ;actual key length
    cmp word ptr [key_len], 0
    je done_xor_checkpoint1 ;nothing to do if empty key
	jmp continue1
	done_xor_checkpoint1:
	jmp done_xor
	continue1:

    ;close key file (we only need in-memory key)
    mov bx, key_handle
    mov ah, 3Eh
    int 21h

    ;initialize key index (si)
    xor si, si

	read_next_chunk:
		;read chunk from data file
		mov bx, data_handle
		mov dx, OFFSET data_content
		mov cx, 512
		call ReadFile
		jc data_read_err
		mov [bytes_read], ax
		cmp word ptr [bytes_read], 0
		je done_xor_checkpoint2 ;EOF
		jmp continue2
		done_xor_checkpoint2:
		jmp done_xor
		continue2:

		;process bytes_read bytes: index in BX, counter in CX
		mov cx, word ptr [bytes_read] ;CX = count
		xor bx, bx ;BX = byte index
	xor_loop:
		mov al, [data_content + bx]
		mov ah, [key_content + si]
		xor al, ah
		mov [res_content + bx], al

		inc bx
		inc si
		mov ax, si
		cmp ax, word ptr [key_len]
		jb xor_no_wrap
		xor si, si
	xor_no_wrap:
		loop xor_loop

		;write processed bytes to res file
		mov bx, res_handle
		mov dx, OFFSET res_content
		mov cx, word ptr [bytes_read] ;number of bytes to write
		call WriteFile
		jc write_err

		jmp read_next_chunk

	key_read_err:
		_NEWLINE
		_SPRINTF err_open_msg
		jmp cleanup

	data_read_err:
		_NEWLINE
		_SPRINTF err_open_msg
		jmp cleanup

	write_err:
		_NEWLINE
		_SPRINTF err_open_msg
		jmp cleanup

	done_xor:
	;----------------------------------------------
	cleanup:
		
		_CLOSE_FILE data_handle
		_CLOSE_FILE key_handle
		_CLOSE_FILE res_handle
		
		_NEWLINE
		_NSPRINTF success_msg
		_CLEAN
		_CLEAN
		_EXIT_DOS
	Main ENDP
	
	ReadFile PROC NEAR
		;BX = handle
		;DX = buffer
		;CX = bytes to read
		mov ah, 3Fh
		int 21h
		ret
	ReadFile ENDP
	
	WriteFile PROC NEAR
		;BX = handle
		;DX = buffer
		;CX = bytes to write
		mov ah, 40h
		int 21h
		ret
	WriteFile ENDP
	
	CALL NEAR PTR Main
end start