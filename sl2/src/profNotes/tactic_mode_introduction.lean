-- boolean and 


-- c-style

def band_c (b1 b2 : bool) : bool :=
    match b1 with
    | tt := match b2 with
            | tt := tt
            | ff := ff
            end
    | ff := ff
    end

-- cases/equations

def band_eqs : bool → bool → bool
| tt tt := tt
| _ _ := ff

-- lambda

def band_lambda : bool → bool → bool :=
λ b1 b2,
  match b1 with
  | tt := match b2 with
          | tt := tt
          | ff := ff
          end
  | ff := ff
  end


-- tactic mode!

def band_tactic : bool → bool → bool :=
begin
assume b1 b2,
cases b1,
exact ff,
cases b2,
exact ff,
exact tt,
end

#check band_tactic
#eval band_tactic tt ff


def is_zero : nat → bool :=
begin
assume n,
cases n with n',
exact tt,
exact ff,
end

#eval is_zero 5


inductive day : Type
| mo
| tu
| we
| th
| fr
| sa
| su

open day

def next_day : day → day :=
begin
assume d,
cases d,
exact tu,
exact we,
exact th,
exact fr,
exact sa,
exact su,
exact mo,
end

#reduce next_day tu