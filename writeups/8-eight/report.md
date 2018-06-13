## A potentially useful tool for benchmarking SQL analysis tools
In order to show the feasibility of using ADSL for benchmarking real-world applications in our tool, I created a very simple ruby test-case where the application makes use of active records and maintains a number of bank accounts. A single function *withdraw* is supported by the application, which decrements the balance of a chosen account by 100:

#####  Model:
``` Ruby
class Account < ActiveRecord::Base
  has_one :balance
  has_one :owner
end
```

##### Controller:
``` Ruby
class AccountsController < ApplicationController
  def withdraw 
    @all_acs = Account.all
    @kia_acs = Account.where(owner: 'Kia')
    @ac1 = @kia_acs.first
    if @ac1.balance >= 100
        then @ac1.balance = @ac1.balance - 100 end
  end
end
```


After applying **adsl** tool directly on the application, we get a very simple model of the application; a model that takes care of the meta language function calls but lacks any form of program logic:
##### Basic ADSL output:
``` Ruby
class Account {
}
action AccountsController__withdraw {
  at__all_acs = Account
  at__kia_acs = subset(Account)
  at__ac1 = tryoneof(at__kia_acs)
  if(*){
  }
}
```


With a little bit of shallow hacking, I was able to upgrade ADSL to a version which can generate the followoing code:
(**note that it is yet far from being a real generic tool**)

##### Modified ADSL output:
``` Ruby
class Account {
}
action AccountsController__withdraw {
  at__all_acs = Account
  at__kia_acs =  subset(Account) such that: [{:owner=>"Kia"}] 
  at__ac1 = oneof(Account) such that: record is the first occurence
  if (at__ac1(balance) >= 100) {
    at__ac1(balance)=at__ac1(balance) - 100
  } 
}
```


As you can see, the above model includes all the necessary information required to transfer the Ruby code to SQL. In other words, the above code is semantically equivalent to SQL; I just had to rewrite it very quickly to the following Ocaml code, before I was able to run my verification tool on it: 


``` Ocaml
(*Tabel Definitions*)
type account = {a_id: int; mutable a_owner: string; mutable a_balance: int}

(*TXNs*)
let withdraw_txn (input:int) =
  let at__all_acs = SQL.select Account A_all
     (fun a -> 1=1) in                             
  let at__kia_acs = SQL.select Account A_all
     (fun a -> a.a_owner = "Kia" ) in
  let at__ac1 = SQL.choose (fun a -> 1=1) at__kia_acs in
  SQL.update Account
    (*do:*)    (fun a -> begin a.a_balance <- a.a_balance - 100; end)
    (*where:*) (fun a -> a.a_id = at__ac1.a_id)
```
 
 By running the tool on the above SQL program, the following z3 file was created, which is satisfiable under EC, RC, CC but not under SI or SER:
https://github.com/Kiarahmani/deSQLifier/blob/master/writeups/8-eight/z3-encoding.smt2
 
 This means that our simple Ruby application would not be correctly running in many off-the-shelf databases (assuming the default isolation levels are used)
 
 | Database        | Default Isolation        | Correct?  |
| ------------- |:-------------:| -----:|
|Actian Ingres     |SER| YES |
|Aerospike | RC      |   NO |
| Greenplum 4.1 | RC      |    NO |
|MySQL 5.6 | RR | NO |
|MS SQL Server 2012  | RC| NO
|VoltDB | SER | YES
|Postgres 9.2.2 | RC | NO
|Oracle 11g | RC | NO
|Akiban Persistit | SI | YES





