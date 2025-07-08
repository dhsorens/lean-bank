import Bank
import Init.System.IO

-- #check IO.ofExcept
-- #check IO.FS.Stream.getLine
-- #check IO.FS.Stream

-- IO versions of create, deposit, withdraw, etc.
def io_open_account (bank : Bank) : Bank × String :=
  match open_account bank with
  | Except.error e =>
    (bank,s!"{e} \n")
  | Except.ok (bank, new_id) =>
    (bank,s!"Opened account number {new_id}.\n")

def io_close_account (id : Nat) (bank : Bank) : Bank × String :=
  match close_account id bank with
  | Except.error e =>
    (bank,s!"{e} \n")
  | Except.ok bank =>
    (bank,s!"Closed account number {id}.\n")

def io_deposit (id_to amt : Nat) (bank : Bank) : Bank × String :=
  match (transact (.Deposit id_to amt) bank) with
  | Except.error e =>
    (bank,s!"{e} \n")
  | Except.ok bank =>
    (bank,s!"Deposited {amt} into account number {id_to}.\n")

def io_withdraw (id_from amt : Nat) (bank : Bank) : Bank × String :=
  match (transact (.Withdraw id_from amt) bank) with
  | Except.error e =>
    (bank,s!"{e} \n")
  | Except.ok bank =>
    (bank,s!"Withdrew {amt} from account number {id_from}.\n")

def io_transfer (id_from id_to amt : Nat) (bank : Bank) : Bank × String :=
  match (transact (.Transfer id_from id_to amt) bank) with
  | Except.error e =>
    (bank,s!"{e} \n")
  | Except.ok bank =>
    (bank,s!"Transferred {amt} from account number {id_from} into account number {id_to}.\n")

def io_bal (id : Nat) (bank : Bank) : Bank × String :=
  match bank_bal id bank with
  | Except.error e =>
    (bank,s!"{e} \n")
  | Except.ok b =>
    (bank,s!"The balance of account {id} is {b}. \n")

-- a CLI loop that lets you deposit, etc. as the bank
partial def cli_loop (bank : Bank) : IO Unit := do
    let stdin ← IO.getStdin
    IO.print "> "
    let line ← IO.FS.Stream.getLine stdin
    let tokens := line.trim.splitOn " "
    match tokens with
    | ["open"] =>
        -- call open function
        let (bank, msg) := io_open_account bank
        IO.print msg
        cli_loop bank
    | ["close", idStr] =>
        match idStr.toNat? with
        | some id =>
            -- call your close function
            let (bank, msg) := io_close_account id bank
            IO.print msg
            cli_loop bank
        | none =>
            IO.println "Error: close expects a natural number."
        cli_loop bank
    | ["deposit", idStr, amtStr] =>
        match idStr.toNat?, amtStr.toNat? with
        | some id, some amt =>
            -- Here you would call your deposit function
            let (bank, msg) := io_deposit id amt bank
            IO.print msg
            cli_loop bank
        | _, _ =>
            IO.println "Error: deposit expects two natural numbers."
        cli_loop bank
    | ["withdraw", idStr, amtStr] =>
        match idStr.toNat?, amtStr.toNat? with
        | some id, some amt =>
            -- Here you would call your withdraw function
            let (bank, msg) := io_withdraw id amt bank
            IO.print msg
            cli_loop bank
        | _, _ =>
            IO.println "Error: withdraw expects two natural numbers."
        cli_loop bank
    | ["transfer", fromStr, toStr, amtStr] =>
        match fromStr.toNat?, toStr.toNat?, amtStr.toNat? with
        | some fromId, some toId, some amt =>
            let (bank, msg) := io_transfer fromId toId amt bank
            IO.print msg
            cli_loop bank
        | _, _, _ =>
            IO.println "Error: transfer expects three natural numbers."
        cli_loop bank
    | ["bal", idStr] =>
      match idStr.toNat? with
      | some id =>
        let (bank, msg) := io_bal id bank
        IO.print msg
        cli_loop bank
      | none =>
        IO.println "Error: bal expects a natural number."
      cli_loop bank
    | ["exit"] =>
        IO.println "Goodbye!"
    | _ =>
        IO.println s!"Try again: {line.trim}"
        cli_loop bank


def main : IO Unit := do
  let bank := init_bank -- initialize the bank
  IO.print "Bleep bleep bloop the bank is open! \n"
  cli_loop bank -- run the CLI
