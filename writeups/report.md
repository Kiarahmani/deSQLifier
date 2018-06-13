I created a very simple ruby test case where the application makes use of active records and maintains a number of bank accounts. One *withdraw* function is supported which decrements the balance of a chosen account by 100.

####  Model:
``` Ruby
class Account < ActiveRecord::Base
  has_one :balance
  has_one :owner
  validates :balance, numericality: { greater_than: 0}
end
```

#### Controller:
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


When applying adsl tool directly on the application, we get a very simple model of the application; a model that takes care of the meta language function calls but langs any form of program logic:
#### Basic ADSL output:
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


With a little bit of shallow hacking, I was able to upgrade ADSL to a version which can generate the follwoing code:
(note that it is yet far from a generic tool)

#### Modified ADSL output:
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


As you can see, the above model includes all the necessary information required to transfer the Ruby code to SQL. In other words, the above code is basically SQL, I just had to rewrite it very easily to the following, before I was able to run my verification tool on it: 







