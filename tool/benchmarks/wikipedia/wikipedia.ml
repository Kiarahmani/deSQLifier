let unimpl () = failwith "Unimpl"

type table_name = 
  |Ip_blocks |User_account |Logging
  |Page |Page_backup |Page_restrictions
  |Recent_changes |Revision |Text
  |User_groups |Value_backup |Watchlist


type column_name = 
  |IB_all |IB_id |IB_address |IB_user |IB_by |IB_bytext |IB_reason |IB_timestamp |IB_auto |IB_anononly |IB_createaccount |IB_enableautoblock
  |IB_expiry |IB_rangestart |IB_rangeend |IB_deleted |IB_blockemail |IB_allowusertalk
  |UA_all |UA_id |UA_name |UA_realname |UA_password |UA_newpassword |UA_newpasstime |UA_email |UA_options |UA_touched |UA_token |UA_emailauthenticated
  |UA_emailtoken |UA_emailtokenexpires |UA_registration |UA_editcount
  |L_all |L_id |L_type |L_action |L_timestamp |L_user |L_namespace |L_title |L_comment |L_params |L_deleted |L_usertext |L_page
  |P_all |P_id |P_namespace |P_title |P_restriction |P_counter |P_isredirect |P_isnew |P_random |P_touched |P_latest |P_len
  |PB_all|PB_id |PB_namespace |PB_title |PB_restriction |PB_counter |PB_isredirect |PB_isnew |PB_random |PB_touched |PB_latest |PB_len
  |PR_all |PR_page |PR_type |PR_level |PR_cascade |PR_user |PR_expiry |PR_id
  |RC_all |RC_id |RC_timestamp |RC_curtime |RC_user |RC_usertext |RC_namespace |RC_title |RC_comment |RC_minor |RC_bot |RC_new |RC_curid |RC_thisoldid
  |RC_lastoldid |RC_type |RC_movedtons |RC_movedtotitle |RC_patrolled |RC_ip |RC_oldlen |RC_newlen |RC_deleted |RC_logid |RC_logtype |RC_logaction
  |RC_params
  |R_all |R_id |R_page |R_textid |R_comment |R_user |R_usertext |R_timestamp |R_minoredit |R_deleted |R_len |R_parentid
  |T_all |T_id |T_text |T_flags |T_page
  |UG_all |UG_user |UG_group
  |VB_all |VB_tablename |VB_maxid
  |W_all |W_user |W_namespace |W_title |W_notificationtimestamp

module SQL: 
sig
  val select1:      table_name -> column_name  -> ('a -> bool) -> 'a
  val select:       table_name -> column_name -> ('a -> bool) -> 'a list
  val select_max:   table_name -> column_name -> ('a -> bool) -> 'a
  val select_min:   table_name -> column_name -> ('a -> bool) -> 'a
  val select_count: table_name -> column_name -> ('a -> bool) -> int
  val insert:       table_name  ->  'a -> unit
  val delete:       table_name  -> ('a -> bool) -> unit
  val update:       table_name  -> ('a -> unit) -> ('a -> bool) -> unit
  val choose:  ('a -> bool) -> 'a list -> 'a
  val foreach: 'a list -> ('a -> unit) -> unit
end = 
struct
  let select = unimpl ()
  let select1 = unimpl ()
  let select_max = unimpl ()
  let select_count = unimpl ()
  let select_min = unimpl ()
  let insert = unimpl ()
  let delete = unimpl ()
  let update = unimpl ()
  let choose = unimpl ()
  let foreach = unimpl ()
end

(*----------------------------------------------------------------------------------------------------*)
type ip_blocks  = {ipb_id:int; mutable ipb_address:string;  mutable ipb_user:int;  mutable ipb_by:int;  mutable ipb_by_text:string;  
                   mutable ipb_reason:string;  mutable ipb_timestamp:string; mutable ipb_auto:int;  mutable ipb_anon_only:int;  mutable ipb_create_account:int;  
                   mutable ipb_enable_autoblock:int;  mutable ipb_expiry:string;  mutable ipb_range_start:string; mutable ipb_range_end:string;  
                   mutable ipb_deleted:int;  mutable ipb_block_email:int;  mutable ipb_allow_usertalk:int}
type user_account = {user_id:int; mutable user_name:string; mutable user_password:string; mutable user_newpassword:string;
                     mutable user_newpass_time:string; mutable user_email:string; mutable user_options:string; mutable user_touched:string; 
                     mutable user_token:string; mutable user_email_authenticated:string; mutable user_email_token:string; mutable user_email_token_expires:string; 
                     mutable user_registration:string; mutable user_editcount:int; user_exists:bool}
type logging = {log_id:int; mutable log_type:string; mutable log_action:string; mutable log_timestamp:string; mutable log_user:int; 
                mutable log_namespace:int; mutable log_title:string; mutable log_comment:string; mutable log_params:string; mutable log_deleted:int; 
                mutable log_user_text:string}
type page = {page_id:int; mutable page_namespace:int; mutable page_title:string; mutable page_restrictions:string; 
             mutable page_counter:int; mutable page_random:int; mutable page_touched:string; 
             mutable page_latest:int; mutable page_len:int; mutable page_isnew:int; mutable page_is_redirect:int}
type page_backup = {page_id:int; mutable page_namespace:int; mutable page_title:string; mutable page_restrictions:string;
             mutable page_counter:int; mutable page_random:int; mutable page_touched:string; 
             mutable page_latest:int; mutable page_len:int; mutable page_isnew:int; mutable page_is_redirect:int}

type page_restrictions = {pr_id:int; mutable pr_page:int; mutable pr_type:string; mutable pr_level:string; mutable pr_cascade:int; mutable pr_user:int; 
                         mutable pr_expiry:string}

type recent_changes = {rc_id:int; mutable rc_timestamp:string; mutable rc_cur_time:string; mutable rc_user:int; mutable rc_user_text:string; mutable
                        rc_namespace:int; mutable rc_title:string; mutable rc_comment:string; mutable rc_minor:int; mutable rc_bot:int; 
                       mutable rc_new:int; mutable rc_cur_id:int; mutable rc_this_oldid:int; mutable rc_last_oldid:int; mutable rc_type:int;
                       mutable rc_moved_to_ns:int; mutable rc_moved_to_title:string; mutable rc_patrolled:int; mutable rc_ip:string; 
                       mutable rc_old_len:int; mutable rc_new_len:int; mutable rc_deleted:int; mutable rc_logid:int; 
                       mutable rc_log_type:string; mutable rc_log_action:string; mutable rc_params:string}
type revision= {rev_id:int; mutable rev_page:int; mutable rev_text_id:int; mutable rev_comment:string; mutable rev_user:int; 
                mutable rev_user_text:string; mutable rev_timestamp:string; mutable rev_minor_edit:int; mutable rev_deleted:int; 
                mutable rev_len:int; mutable rev_parent_id:int}
type text = {old_id:int; mutable old_text:string; mutable old_flags:string; mutable old_page:int}
type user_groups = {ug_user:int; ug_group:string}
type value_backup = {table_name:string; maxid:int}
type watchlist = {wl_user:int; wl_namespace:int; wl_title:string; mutable wl_notificationtimestamp:string; mutable wl_exists:bool}
(*----------------------------------------------------------------------------------------------------*)


(*--------------------*)
(*TXN1: getPageAnonymous*)
let get_page_anonymous_txn (input_userIp:string) (input_forSelect:bool) (input_pageNamespace:int) (input_pageTitle:string) =
  (*select page*)
  let v1 = SQL.select Page P_all (fun u -> u.page_namespace = input_pageNamespace && u.page_title = input_pageTitle) in
  let v2 = SQL.choose (fun u -> 1=1) v1 in
  (*select page restrictions*)
  let v3 = SQL.select1 Page_restrictions PR_all (fun u -> u.pr_page=v2.page_id) in
  (*select ip blocks*)
  let v4 = SQL.select1 Ip_blocks IB_all (fun u -> u.ipb_address = input_userIp) in
  (*select page revisions*)
  let v5 = SQL.select1 Revision R_all (fun u -> u.rev_page = v2.page_id && u.rev_id = v2.page_latest) in
  ()

(*--------------------*)
(*TXN2: getPageAuthenticated*)
let get_page_authenticated_txn (input_forSelect:bool)(input_userIp:string)(input_userId:int)(input_nameSpace:int)(input_pageTitle:string) =
  if (input_userId>0)
  then 
    let v1 = SQL.select1 User_account UA_all (fun u -> u.user_id = input_userId) in
    if (v1.user_exists=true)
    then( 
      let v2 =SQL.select User_groups UG_group (fun u -> u.ug_user = input_userId) in
      SQL.foreach v2 
        begin fun v2_loop_var_1 ->
          () (*print group name*)
        end;
      let v3 = SQL.select Page P_all (fun u -> u.page_namespace = input_nameSpace && u.page_title = input_pageTitle) in
      let v4 = SQL.choose (fun u -> 1=1) v3 in
      (*select page restrictions*)
      let v5 = SQL.select1 Page_restrictions PR_all (fun u -> u.pr_page=v4.page_id) in
      (*select ip blocks*)
      let v6 = SQL.select1 Ip_blocks IB_all (fun u -> u.ipb_address = input_userIp) in
      (*select page revisions*)
      let v7 = SQL.select1 Revision R_all (fun u -> u.rev_page = v4.page_id && u.rev_id = v4.page_latest) in
      ()
    )



(*--------------------*)
(*TXN3: addToWatchlist*)
let add_to_watchlist_txn (input_userId:int)(input_nameSpace:int)(input_pageTitle:string) =
  if (input_userId>0)
  then(
    let v1 = SQL.select1 Watchlist W_all (fun u -> u.wl_user=input_userId && u.wl_namespace=input_nameSpace && u.wl_title=input_pageTitle) in
    (if (v1.wl_exists=false)
    then (SQL.insert Watchlist {wl_user=input_userId; wl_namespace=input_nameSpace; wl_title=input_pageTitle; wl_notificationtimestamp="";
                                wl_exists=true}));
    (if (input_nameSpace=0)
    then 
      let v2 = SQL.select1 Watchlist W_all (fun u -> u.wl_user=input_userId && u.wl_namespace=1 && u.wl_title=input_pageTitle) in
      if (v1.wl_exists=false)
      then (SQL.insert Watchlist {wl_user=input_userId; wl_namespace=1; wl_title=input_pageTitle; wl_notificationtimestamp="";
                                  wl_exists=true}));
    SQL.update User_account
        (*do:*)    (fun u -> begin u.user_touched <- "9/11/2018"; end)
        (*where:*) (fun u -> u.user_id = input_userId)
  )



(*--------------------*)
(*TXN4: removeFromWatchlist*)
let remove_from_watchlist_txn (input_userId:int)(input_nameSpace:int)(input_pageTitle:string) =
  if (input_userId>0)
  then(
    SQL.delete Watchlist (fun u -> u.wl_user=input_userId && u.wl_namespace=input_nameSpace && u.wl_title=input_pageTitle);
    (if (input_nameSpace=0)
     then  SQL.delete Watchlist (fun u -> u.wl_user=input_userId && u.wl_namespace=2 && u.wl_title=input_pageTitle)); 
    SQL.update User_account
        (*do:*)    (fun u -> begin u.user_touched <- "9/11/2018"; end)
        (*where:*) (fun u -> u.user_id = input_userId)
    )





(*--------------------*)
(*TXN5: updatePage*)
let update_page_txn (input_textId:int)(input_pageId:int)(input_pageTitle:string)(input_pageText:string)(input_pageText_length:int)(input_pageNamespace:int)
                    (input_userId:int)(input_userIp:string)(input_userText:string)(input_revisionId:int)(input_revComment:string)
                    (input_revMinorEdit:int) =
  let v1 = SQL.select1 Text T_id (fun u -> 1=1) in
  SQL.insert Text {old_id=v1.old_id+1; old_text=input_pageText; old_flags="utf-8"; old_page=input_pageId};
  let v2 = SQL.select1 Revision R_id (fun u -> 1=1) in
  SQL.insert Revision {rev_id=v2.rev_id+1; rev_page=input_pageId; rev_text_id=v1.old_id+1; rev_comment=input_revComment; rev_user=input_userId;
                       rev_user_text=input_userText; rev_timestamp="9/11/2018"; rev_minor_edit=input_revMinorEdit; rev_deleted=0;
                       rev_len=input_pageText_length; rev_parent_id=input_revisionId};
  SQL.update Page
    (*do:*)    (fun u -> begin u.page_latest<-v2.rev_id+1; end)
    (*where:*) (fun u -> u.page_id = input_pageId);
(*  SQL.update Page
    (*do:*)    (fun u -> begin u.page_touched<-"9/11/18"; end)
    (*where:*) (fun u -> u.page_id = input_pageId);
  SQL.update Page
    (*do:*)    (fun u -> begin u.page_isnew<-0; end)
    (*where:*) (fun u -> u.page_id = input_pageId);
  SQL.update Page
    (*do:*)    (fun u -> begin  u.page_is_redirect<-0; end)
    (*where:*) (fun u -> u.page_id = input_pageId);
  SQL.update Page
  (*do:*)    (fun u -> begin u.page_len<-input_pageText_length; end)
    (*where:*) (fun u -> u.page_id = input_pageId);
*)
  let v3 = SQL.select1 Recent_changes RC_id (fun u -> 1=1) in
  SQL.insert Recent_changes {rc_id=v3.rc_id+1; rc_timestamp="9/11/2018"; rc_cur_time="9/11/2018"; rc_user=input_userId; rc_user_text=input_userText; 
                        rc_namespace=input_pageNamespace; rc_title=input_pageTitle; rc_comment=input_revComment; rc_minor=0; rc_bot=0;
                        rc_new=input_pageText_length; rc_cur_id=input_pageId; rc_this_oldid=v1.old_id+1; rc_last_oldid=v1.old_id; rc_type=0;
                        rc_moved_to_ns=0; rc_moved_to_title=""; rc_patrolled=0; rc_ip=input_userIp;
                        rc_old_len=input_pageText_length; rc_new_len=input_pageText_length; rc_deleted=0; rc_logid=0;
                             rc_log_type=""; rc_log_action=""; rc_params=""};
  let v4 = SQL.select Watchlist W_user (fun u -> u.wl_title = input_pageTitle && u.wl_namespace = input_pageNamespace && u.wl_user = input_userId) in
  SQL.foreach v4
    begin fun v4_loop_var_1 ->
      let v5 = SQL.select1 User_account UA_all (fun u -> u.user_id=v4_loop_var_1.wl_user) in
      SQL.update Watchlist
      (*do:*)    (fun u -> begin u.wl_notificationtimestamp<-"9/11/2018"; end)
      (*where:*) (fun u -> u.wl_title = input_pageTitle && u.wl_namespace = input_pageNamespace && u.wl_user = v4_loop_var_1.wl_user);
    end;
  let v6 = SQL.select1 Logging L_id (fun u -> 1=1) in
  SQL.insert Logging  {log_id=v6.log_id+1; log_type="patrol"; log_action="patrol"; log_timestamp="9/11/2018"; log_user=input_userId;
                        log_namespace=input_pageNamespace; log_title=input_pageTitle; log_comment=""; log_params=""; log_deleted=0;
                       log_user_text=input_userText};
  let v7 = SQL.select1 User_account UA_editcount (fun u -> u.user_id = input_userId) in
  SQL.update User_account
    (*do:*)    (fun u -> begin u.user_editcount<-v7.user_editcount+1; end)
    (*where:*) (fun u -> u.user_id = input_userId);
  SQL.update User_account
    (*do:*)    (fun u -> begin u.user_touched <- "9/11/2018" ; end)
    (*where:*) (fun u -> u.user_id = input_userId)
  
