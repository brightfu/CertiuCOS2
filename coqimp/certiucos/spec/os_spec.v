Require Import os_program.
Require Import abs_op.
Require Import include_frm.
Require Import os_code_defs.

Local Open Scope list_scope.

Definition api_spec_list := 
  (OSQAccept,qaccapi) ::
  (OSQCreate,qcreapi) ::
  (OSQDel, qdelapi) ::
  (OSQPend,qpendapi) ::
  (OSQGetMsg, getmsgapi) ::
  (OSQPost,qpostapi) ::
  (OSSemAccept, semaccapi) ::
  (OSSemCreate, semcreapi) ::
  (OSSemDel, semdelapi) ::
  (OSSemPend, sem_pendapi) ::
  (OSSemPost, sem_postapi) :: 
  (OSTimeDly, dlyapi) ::
  (OSTimeGet, tmgetapi) ::
  (OSMboxCreate, mbox_createapi) ::
  (OSMboxDel, mbox_delapi) ::
  (OSMboxAccept, mbox_accapi) ::
  (OSMboxPend, mbox_pendapi) ::
  (OSMboxPost, mbox_postapi) ::
  (OSMutexCreate, mutexcreapi) ::
  (OSMutexDel, mutexdelapi) ::
  (OSMutexAccept, mutexaccapi) ::
  (OSMutexPend, mutexpendapi) ::
  (OSMutexPost, mutexpostapi) ::
  (OSTaskCreate, taskcreapi) :: 
  (OSTaskDel, taskdelapi) :: 
  nil.


Fixpoint convert_api_spec (ls : list (fid * osapi)) : fid -> option osapi :=
  match ls with
    | nil => fun _ : fid => None
    | (id, imp) :: ls' =>
      fun id' : fid =>
        if Zbool.Zeq_bool id id' then Some imp 
        else convert_api_spec ls' id'
  end.


Definition api_spec := convert_api_spec api_spec_list.

Definition int_spec_list := (OSTickISR, timetick) :: (OSToyISR,toyint) :: nil .

Fixpoint convert_int_spec (ls : list (hid * int_code)) : hid -> option int_code :=
  match ls with
    | nil => fun _ : hid => None
    | (id, imp) :: ls' =>
      fun id' : hid =>
        if EqNat.beq_nat id id' then Some imp 
        else convert_int_spec ls' id'
  end.


Definition int_spec  := convert_int_spec int_spec_list.

Definition os_spec :osspec:=(api_spec,int_spec,GetHPrio).


