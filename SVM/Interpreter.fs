module Interpreter
open SVMAST

// Abbrev legend
// a, a', ... : any first value / address
// b, b', ... : any second value
// d: destination
// e: element
// f: float value
// h: head of list
// l: label / left element / list
// i: index / integer value
// r: register / right element
// s: string value / source
// t: tail of list
// v: value

let typeErr() = invalidOp "Invalid operation on instruction"

type Value = 
    | Flt of float 
    | Int of int 
    | Str of string
    | Nil of unit
        member this.Cmp (v:Value) = 
            let f a b = if a < b then -1 elif a = b then 0 else 1
            match this,v with
            | Int(a'),Int(b') ->  f a' b' 
            | Flt(a'),Flt(b') ->  f a' b' 
            | Int(b'),Flt(a') | Flt(a'),Int(b') ->  f a' (float b') 
            | _-> typeErr()

        static member (+) (a:Value,b:Value) = 
            match a,b with
            | Int(a'),Int(b') -> Value.Int(a' + b')
            | Flt(a'),Flt(b') -> Value.Flt(a' + b')
            | Int(a'),Flt(b') | Flt(b'),Int(a') -> Value.Flt(float a' + b')
            | _-> typeErr()
    
        static member (-) (a:Value,b:Value) = 
            match a,b with
            | Int(a'),Int(b') -> Value.Int(a' - b')
            | Flt(a'),Flt(b') -> Value.Flt(a' - b')
            | Int(a'),Flt(b') | Flt(b'),Int(a') -> Value.Flt(float a' - b')
            | _-> typeErr()
    
        static member (/) (a:Value,b:Value) = 
            match a,b with
            | Int(a'),Int(b') -> Value.Int(a' / b')
            | Flt(a'),Flt(b') -> Value.Flt(a' / b')
            | Int(a'),Flt(b') | Flt(b'),Int(a') -> Value.Flt(float a' / b')
            | _-> typeErr()
    
        static member (*) (a:Value,b:Value) = 
            match a,b with
            | Int(a'),Int(b') -> Value.Int(a' * b')
            | Flt(a'),Flt(b') -> Value.Flt(a' * b')
            | Int(a'),Flt(b') | Flt(b'),Int(a') -> Value.Flt(float a' * b')
            | _-> typeErr()
    
        static member (%) (a:Value,b:Value) = 
            match a,b with
            | Int(a'),Int(b') -> Value.Int(a' % b')
            | Flt(a'),Flt(b') -> Value.Flt(a' % b')
            | Int(b'),Flt(a') | Flt(a'), Int(b') -> Value.Flt(a' % float b')
            | _-> typeErr()

        static member op_GreaterThan (a:Value,b:Value) = 
            match a,b with
            |Int(a'), Int(b') -> a' > b'
            |Flt(a'), Flt(b') -> a' > b'
            |Flt(a'), Int(b') | Int(b'),Flt(a') -> float b' > a'
            | _ -> typeErr()

        static member op_LessThan (a:Value,b:Value) = 
            match a,b with
            |Int(a'), Int(b') -> a' < b'
            |Flt(a'), Flt(b') -> a' < b'
            |Flt(a'), Int(b') | Int(b'),Flt(a') -> float b' < a'
            | _ -> typeErr()

        override Value.ToString() = 
            match Value with
            |Int(i) -> sprintf "%i" i
            |Flt(f) -> sprintf "%.2f" f
            |Str(s) -> s
            |Nil(_) -> "nil"
            
type Registers = { RegA:Value; RegB:Value; RegC:Value; RegD:Value} with
    member this.Get (dest:Register) = 
        match dest with
        | Reg1 -> this.RegA
        | Reg2 -> this.RegB
        | Reg3 -> this.RegC
        | Reg4 -> this.RegD

    member this.SetValue (dest:Register) (srcVal:Value) = 
        match dest with
        | Reg1 -> {RegA = srcVal; RegB = this.RegB; RegC = this.RegC; RegD = this.RegD} 
        | Reg2 -> {RegA = this.RegA; RegB = srcVal; RegC = this.RegC; RegD = this.RegD} 
        | Reg3 -> {RegA = this.RegA; RegB = this.RegB; RegC = srcVal; RegD = this.RegD} 
        | Reg4 -> {RegA = this.RegA; RegB = this.RegB; RegC = this.RegC; RegD = srcVal}
        
type State = { Registers: Registers; Memory:Value list; IP:int; Labels:Map<string,int>} with
    member this.AlterRegs r v = {Registers=this.Registers.SetValue r v; Memory=this.Memory; IP = this.IP; Labels=this.Labels}
    member this.AlterMem mem = {Registers=this.Registers; Memory=mem; IP = this.IP; Labels=this.Labels}
    member this.AlterIP ip = {Registers=this.Registers; Memory=this.Memory; IP = ip; Labels=this.Labels}
    member this.Jump name = this.AlterIP this.Labels.[name]
    static member IncIP (state:State) : State = state.AlterIP (state.IP+1)

module private Helpers = 
    let memlocFromReg (reg:Register) state : int = 
        match state.Registers.Get reg with 
        | Int(i) -> i
        | _ -> typeErr()

    let getMem src state = 
        match src with 
        | Register(r,_) -> state.Memory.[memlocFromReg r state]
        | Integer(i,_) -> state.Memory.[i] 
        | _ -> typeErr()
    
    let getLitVal state src = 
        match src with
        | Register(r,_) -> state.Registers.Get r
        | Address(a) -> getMem a state
        | Float(f,_) -> Flt f
        | Integer(i,_) -> Int i
        | String(s,_) -> Str s
                
    let setMem dest src state = 
        let rec step i d h t = 
            if i = d
            then h @ ((getLitVal state src) :: (List.tail t)) 
            else step (i+1) d (h @ [List.head t] ) (List.tail t)

        match dest with
        | Register(reg,_) -> step 0 (memlocFromReg reg state) [] state.Memory |> state.AlterMem
        | Integer(destAddress,_) -> step 0 destAddress [] state.Memory |> state.AlterMem
        | _ -> typeErr() 
    
    let compare d s (f:Value->Value->int) (state:State) = 
        state.AlterRegs d ( Value.Int ( f (state.Registers.Get d) (getLitVal state s) ) )

    let calculate d s (f:Value->Value->Value) (state:State) = 
        state.AlterRegs d ( f (state.Registers.Get d) (getLitVal state s))
        
    let conJump l r (f:int->bool) state = if f ((state.Registers.Get r).Cmp(Value.Int 0)) then state.Jump l else state
         
    let initVal = Int 0
    let prepare size labels = 
        let rec createList l = if List.length l < size then createList ( (initVal)::l ) else l
        {Registers = {RegA = initVal; RegB = initVal; RegC = initVal; RegD = initVal; }; Memory = createList []; IP = 0; Labels=labels }
        
    let evaluate (ins:SVMAST.Instruction) (state:State) : State = 
        try
            match ins with
            | Nop(_)     -> state
            | Mov(d,s,_) -> match d with
                            | Register(r,_) -> state.AlterRegs r (getLitVal state s)
                            | Address(a) -> setMem a s state
                            | _ -> typeErr()
            | And(d,s,_) -> compare d s (fun d' s' -> if d' < Value.Int 0 && s' < Value.Int 0 then 0 else 1) state
            | Or(d,s,_)  -> compare d s (fun d' s' -> if d' < Value.Int 0 && s' < Value.Int 0 then 0 else 1) state
            | Not(d,p)   -> compare d (Literal.Integer(0,p)) (fun i1 _ -> if i1 > Value.Int 0 then -1 else 0) state 
            | Mod(d,s,_) -> calculate d s (fun i j -> i % j) state
            | Add(d,s,_) -> calculate d s (fun i j -> i + j) state
            | Sub(d,s,_) -> calculate d s (fun i j -> i - j) state
            | Mul(d,s,_) -> calculate d s (fun i j -> i * j) state
            | Div(d,s,_) -> calculate d s (fun i j -> i / j) state
            | Label(l,_) -> state
            | Jmp(l,_)   -> state.Jump l
            | Jc(l,r,_)  -> conJump l r (fun i -> i > 0) state
            | Jeq(l,r,_) -> conJump l r (fun i -> i = 0) state
            | Cmp(l,r,p) -> compare l r (fun l' r' -> l'.Cmp(r')) state
        with 
        | :? System.InvalidOperationException as ex -> 
            ex.Data.Add("Program state", state)
            raise ex

let Run (stackSize) (codeSegment:SVMAST.Program) = 
    
    //Multi-pass for easy labels
    let labels = 
        let rec step i (map:Map<string,int>) l =
            match l with
            | [] -> map
            | x::xs -> step (i+1) ( match x with | Label(l,_) -> map.Add(l,i) | _ -> map ) xs
        step 0 Map.empty codeSegment
    let codeSize = List.length codeSegment
    let rec eval state = if (state.IP) < codeSize then eval (Helpers.evaluate codeSegment.[state.IP] state |> State.IncIP) else state
    let finalState = eval (Helpers.prepare stackSize labels)
    let sep() = printf "\n-----------------\n"
    
    sep()
    printf "<MEMORY>\n"
    List.iteri (fun i (e:Value) -> printf (if i % 10 = 9 then "%s\n" else "%s\t")  (e.ToString())) finalState.Memory
    sep()
    printf "<REGISTERS>\n"
    printf "%A\n" finalState.Registers
    sep()
    printf "<INSTRUCTION POINTER>\n"
    printf "%A\n" finalState.IP