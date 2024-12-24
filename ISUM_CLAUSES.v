Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ISUM_CLAUSES_term_abbrevs.
Require Import ITERATE_CLAUSES_spec.
Require Import MONOIDAL_INT_ADD_spec.
Require Import NEUTRAL_INT_ADD_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm6914165_spec.
Require Import thm6914179_spec.
Require Import thm7_spec.
Lemma lem6918946 : (@monoidal int int_add) = ((@monoidal int int_add) = True).
Proof. exact (@lem7 (@monoidal int int_add)). Qed.
Lemma lem6918948 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6918949 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6918948 _120477 _120519 _120521 h1 op). Qed.
Lemma lem6918950 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6918951 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6918950 _120477 _120519 _120521 op) (@lem6918949 _120477 _120519 _120521 op h1)). Qed.
Lemma lem6918952 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6918953 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6918951 _120477 _120519 _120521 op h1 (@lem6918952 _120519 op h2)). Qed.
Lemma lem6918954 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term4 _120477 _120519 _120521 op.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6918953 _120477 _120519 _120521 op h0 h1). Qed.
Lemma lem6918955 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (h1). Qed.
Lemma lem6918956 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) (h2 : @monoidal _120519 op) : term3 _120477 _120519 _120521 op.
Proof. exact (@lem6918954 _120477 _120519 _120521 op h2 (@lem6918955 _120477 _120519 _120521 h1)). Qed.
Lemma lem6918957 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : term0 _120477 _120519 _120521) : term2 _120477 _120519 _120521 op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6918956 _120477 _120519 _120521 op h1 h0). Qed.
Lemma lem6918958 {_120477 _120519 _120521 : Type'} (h1 : term0 _120477 _120519 _120521) : term0 _120477 _120519 _120521.
Proof. exact (fun op : type1400 _120519 => @lem6918957 _120477 _120519 _120521 op h1). Qed.
Lemma lem6918959 {_120477 _120519 _120521 : Type'} : term5 _120477 _120519 _120521.
Proof. exact (fun h0 : term0 _120477 _120519 _120521 => @lem6918958 _120477 _120519 _120521 h0). Qed.
Lemma lem6918960 {_120477 _120519 _120521 : Type'} : term0 _120477 _120519 _120521.
Proof. exact (@lem6918959 _120477 _120519 _120521 (@lem5753565 _120477 _120519 _120521)). Qed.
Lemma lem6918961 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term1 _120477 _120519 _120521 op.
Proof. exact (@lem6918960 _120477 _120519 _120521 op). Qed.
Lemma lem6918962 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term1 _120477 _120519 _120521 op) = (term2 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term1 _120477 _120519 _120521 op)). Qed.
Lemma lem6918964 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem6918965 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem6918967 (h1 : (@neutral int int_add) = term9) : (@neutral int int_add) = term9.
Proof. exact (h1). Qed.
Lemma lem6918968 (h1 : (@neutral int int_add) = term9) : term9 = (@neutral int int_add).
Proof. exact (SYM (@lem6918967 h1)). Qed.
Lemma lem6918969 (h1 : term9 = (@neutral int int_add)) : term9 = (@neutral int int_add).
Proof. exact (h1). Qed.
Lemma lem6918970 (h1 : term9 = (@neutral int int_add)) : (@neutral int int_add) = term9.
Proof. exact (SYM (@lem6918969 h1)). Qed.
Lemma lem6918971 : ((@neutral int int_add) = term9) = (term9 = (@neutral int int_add)).
Proof. exact (prop_ext (fun h1 : (@neutral int int_add) = term9 => @lem6918968 h1) (fun h1 : term9 = (@neutral int int_add) => @lem6918970 h1)). Qed.
Lemma lem6918982 {_126338 : Type'} : (@isum _126338) = (@iterate int _126338 int_add).
Proof. exact (TRANS (@lem6914165 _126338) (@lem6914179 _126338)). Qed.
Lemma lem6918983 {_126367 : Type'} : (@isum _126367) = (@iterate int _126367 int_add).
Proof. exact (@lem6918982 _126367). Qed.
Lemma lem6918984 {_126367 : Type'} : (@EMPTY _126367) = (@EMPTY _126367).
Proof. exact (eq_refl (@EMPTY _126367)). Qed.
Lemma lem6918985 {_126367 : Type'} : (@isum _126367 (@EMPTY _126367)) = (@iterate int _126367 int_add (@EMPTY _126367)).
Proof. exact (MK_COMB (@lem6918983 _126367) (@lem6918984 _126367)). Qed.
Lemma lem6918986 {_126367 : Type'} (f : _126367 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6918987 {_126367 : Type'} (f : _126367 -> int) : (@isum _126367 (@EMPTY _126367) f) = (@iterate int _126367 int_add (@EMPTY _126367) f).
Proof. exact (MK_COMB (@lem6918985 _126367) (@lem6918986 _126367 f)). Qed.
Lemma lem6918988 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6918989 {_126367 : Type'} (f : _126367 -> int) : (term10 _126367 f) = (term11 _126367 f).
Proof. exact (MK_COMB (@lem6918988) (@lem6918987 _126367 f)). Qed.
Lemma lem6918991 : term9 = (@neutral int int_add).
Proof. exact (EQ_MP (@lem6918971) (@lem6915506)). Qed.
Lemma lem6918992 {_126367 : Type'} (f : _126367 -> int) : ((@isum _126367 (@EMPTY _126367) f) = term9) = ((@iterate int _126367 int_add (@EMPTY _126367) f) = (@neutral int int_add)).
Proof. exact (MK_COMB (@lem6918989 _126367 f) (@lem6918991)). Qed.
Lemma lem6918995 {_126367 : Type'} : (term12 _126367) = (term13 _126367).
Proof. exact (fun_ext (fun f : _126367 -> int => @lem6918992 _126367 f)). Qed.
Lemma lem6918996 {_126367 : Type'} : (@all (_126367 -> int)) = (@all (_126367 -> int)).
Proof. exact (eq_refl (@all (_126367 -> int))). Qed.
Lemma lem6918997 {_126367 : Type'} : (term14 _126367) = (term15 _126367).
Proof. exact (MK_COMB (@lem6918996 _126367) (@lem6918995 _126367)). Qed.
Lemma lem6919002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6919003 {_126367 : Type'} : (term16 _126367) = (term17 _126367).
Proof. exact (MK_COMB (@lem6919002) (@lem6918997 _126367)). Qed.
Lemma lem6919021 {_126338 : Type'} : (@isum _126338) = (@iterate int _126338 int_add).
Proof. exact (TRANS (@lem6914165 _126338) (@lem6914179 _126338)). Qed.
Lemma lem6919022 {_126408 : Type'} : (@isum _126408) = (@iterate int _126408 int_add).
Proof. exact (@lem6919021 _126408). Qed.
Lemma lem6919023 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) : (@INSERT _126408 x s) = (@INSERT _126408 x s).
Proof. exact (eq_refl (@INSERT _126408 x s)). Qed.
Lemma lem6919024 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) : (term18 _126408 x s) = (term19 _126408 x s).
Proof. exact (MK_COMB (@lem6919022 _126408) (@lem6919023 _126408 x s)). Qed.
Lemma lem6919025 {_126408 : Type'} (f : _126408 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6919026 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) (f : _126408 -> int) : (term20 _126408 x s f) = (term21 _126408 x s f).
Proof. exact (MK_COMB (@lem6919024 _126408 x s) (@lem6919025 _126408 f)). Qed.
Lemma lem6919027 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6919028 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) (f : _126408 -> int) : (term22 _126408 x s f) = (term23 _126408 x s f).
Proof. exact (MK_COMB (@lem6919027) (@lem6919026 _126408 x s f)). Qed.
Lemma lem6919030 {_126338 : Type'} : (@isum _126338) = (@iterate int _126338 int_add).
Proof. exact (TRANS (@lem6914165 _126338) (@lem6914179 _126338)). Qed.
Lemma lem6919031 {_126408 : Type'} : (@isum _126408) = (@iterate int _126408 int_add).
Proof. exact (@lem6919030 _126408). Qed.
Lemma lem6919032 {_126408 : Type'} (s : _126408 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6919033 {_126408 : Type'} (s : _126408 -> Prop) : (@isum _126408 s) = (@iterate int _126408 int_add s).
Proof. exact (MK_COMB (@lem6919031 _126408) (@lem6919032 _126408 s)). Qed.
Lemma lem6919034 {_126408 : Type'} (f : _126408 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6919035 {_126408 : Type'} (s : _126408 -> Prop) (f : _126408 -> int) : (@isum _126408 s f) = (@iterate int _126408 int_add s f).
Proof. exact (MK_COMB (@lem6919033 _126408 s) (@lem6919034 _126408 f)). Qed.
Lemma lem6919036 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) : (term24 _126408 x s) = (term24 _126408 x s).
Proof. exact (eq_refl (term24 _126408 x s)). Qed.
Lemma lem6919037 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) (f : _126408 -> int) : (term25 _126408 x s f) = (term26 _126408 x s f).
Proof. exact (MK_COMB (@lem6919036 _126408 x s) (@lem6919035 _126408 s f)). Qed.
Lemma lem6919039 {_126338 : Type'} : (@isum _126338) = (@iterate int _126338 int_add).
Proof. exact (TRANS (@lem6914165 _126338) (@lem6914179 _126338)). Qed.
Lemma lem6919040 {_126408 : Type'} : (@isum _126408) = (@iterate int _126408 int_add).
Proof. exact (@lem6919039 _126408). Qed.
Lemma lem6919041 {_126408 : Type'} (s : _126408 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6919042 {_126408 : Type'} (s : _126408 -> Prop) : (@isum _126408 s) = (@iterate int _126408 int_add s).
Proof. exact (MK_COMB (@lem6919040 _126408) (@lem6919041 _126408 s)). Qed.
Lemma lem6919043 {_126408 : Type'} (f : _126408 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6919044 {_126408 : Type'} (s : _126408 -> Prop) (f : _126408 -> int) : (@isum _126408 s f) = (@iterate int _126408 int_add s f).
Proof. exact (MK_COMB (@lem6919042 _126408 s) (@lem6919043 _126408 f)). Qed.
Lemma lem6919045 {_126408 : Type'} (f : _126408 -> int) (x : _126408) : (term27 _126408 f x) = (term27 _126408 f x).
Proof. exact (eq_refl (term27 _126408 f x)). Qed.
Lemma lem6919046 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) (f : _126408 -> int) : (term28 _126408 x s f) = (term29 _126408 x s f).
Proof. exact (MK_COMB (@lem6919045 _126408 f x) (@lem6919044 _126408 s f)). Qed.
Lemma lem6919047 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) (f : _126408 -> int) : (term30 _126408 x s f) = (term31 _126408 x s f).
Proof. exact (MK_COMB (@lem6919037 _126408 x s f) (@lem6919046 _126408 x s f)). Qed.
Lemma lem6919048 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) (f : _126408 -> int) : ((term20 _126408 x s f) = (term30 _126408 x s f)) = ((term21 _126408 x s f) = (term31 _126408 x s f)).
Proof. exact (MK_COMB (@lem6919028 _126408 x s f) (@lem6919047 _126408 x s f)). Qed.
Lemma lem6919051 {_126408 : Type'} (s : _126408 -> Prop) : (term32 _126408 s) = (term32 _126408 s).
Proof. exact (eq_refl (term32 _126408 s)). Qed.
Lemma lem6919052 {_126408 : Type'} (x : _126408) (s : _126408 -> Prop) (f : _126408 -> int) : (term33 _126408 x s f) = (term34 _126408 x s f).
Proof. exact (MK_COMB (@lem6919051 _126408 s) (@lem6919048 _126408 x s f)). Qed.
Lemma lem6919055 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term35 _126408 x f) = (term36 _126408 x f).
Proof. exact (fun_ext (fun s : _126408 -> Prop => @lem6919052 _126408 x s f)). Qed.
Lemma lem6919056 {_126408 : Type'} : (@all (_126408 -> Prop)) = (@all (_126408 -> Prop)).
Proof. exact (eq_refl (@all (_126408 -> Prop))). Qed.
Lemma lem6919057 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term37 _126408 x f) = (term38 _126408 x f).
Proof. exact (MK_COMB (@lem6919056 _126408) (@lem6919055 _126408 x f)). Qed.
Lemma lem6919062 {_126408 : Type'} (x : _126408) : (term39 _126408 x) = (term40 _126408 x).
Proof. exact (fun_ext (fun f : _126408 -> int => @lem6919057 _126408 x f)). Qed.
Lemma lem6919063 {_126408 : Type'} : (@all (_126408 -> int)) = (@all (_126408 -> int)).
Proof. exact (eq_refl (@all (_126408 -> int))). Qed.
Lemma lem6919064 {_126408 : Type'} (x : _126408) : (term41 _126408 x) = (term42 _126408 x).
Proof. exact (MK_COMB (@lem6919063 _126408) (@lem6919062 _126408 x)). Qed.
Lemma lem6919069 {_126408 : Type'} : (term43 _126408) = (term44 _126408).
Proof. exact (fun_ext (fun x : _126408 => @lem6919064 _126408 x)). Qed.
Lemma lem6919070 {_126408 : Type'} : (@all _126408) = (@all _126408).
Proof. exact (eq_refl (@all _126408)). Qed.
Lemma lem6919071 {_126408 : Type'} : (term45 _126408) = (term46 _126408).
Proof. exact (MK_COMB (@lem6919070 _126408) (@lem6919069 _126408)). Qed.
Lemma lem6919076 {_126367 _126408 : Type'} : (term47 _126367 _126408) = (term48 _126367 _126408).
Proof. exact (MK_COMB (@lem6919003 _126367) (@lem6919071 _126408)). Qed.
Lemma lem6919079 {_126367 _126408 : Type'} : (term48 _126367 _126408) = (term47 _126367 _126408).
Proof. exact (SYM (@lem6919076 _126367 _126408)). Qed.
Lemma lem6919089 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem6918965 A B P) (@lem6918964 A B P)). Qed.
Lemma lem6919090 {_126408 : Type'} (P : type1365 _126408) : (term49 _126408 P) = (term50 _126408 P).
Proof. exact (@lem6919089 _126408 (_126408 -> int) P). Qed.
Lemma lem6919091 {_126408 : Type'} : (term51 _126408) = (term52 _126408).
Proof. exact (@lem6919090 _126408 (term53 _126408)). Qed.
Lemma lem6919092 {_126408 : Type'} (x : _126408) : (term54 _126408 x) = (term40 _126408 x).
Proof. exact (eq_refl (term54 _126408 x)). Qed.
Lemma lem6919093 {_126408 : Type'} (f : _126408 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6919094 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term55 _126408 x f) = (term56 _126408 x f).
Proof. exact (MK_COMB (@lem6919092 _126408 x) (@lem6919093 _126408 f)). Qed.
Lemma lem6919095 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term56 _126408 x f) = (term38 _126408 x f).
Proof. exact (eq_refl (term56 _126408 x f)). Qed.
Lemma lem6919096 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term55 _126408 x f) = (term38 _126408 x f).
Proof. exact (TRANS (@lem6919094 _126408 x f) (@lem6919095 _126408 x f)). Qed.
Lemma lem6919097 {_126408 : Type'} (x : _126408) : (term57 _126408 x) = (term40 _126408 x).
Proof. exact (fun_ext (fun f : _126408 -> int => @lem6919096 _126408 x f)). Qed.
Lemma lem6919098 {_126408 : Type'} : (@all (_126408 -> int)) = (@all (_126408 -> int)).
Proof. exact (eq_refl (@all (_126408 -> int))). Qed.
Lemma lem6919099 {_126408 : Type'} (x : _126408) : (term58 _126408 x) = (term42 _126408 x).
Proof. exact (MK_COMB (@lem6919098 _126408) (@lem6919097 _126408 x)). Qed.
Lemma lem6919100 {_126408 : Type'} : (term59 _126408) = (term44 _126408).
Proof. exact (fun_ext (fun x : _126408 => @lem6919099 _126408 x)). Qed.
Lemma lem6919101 {_126408 : Type'} : (@all _126408) = (@all _126408).
Proof. exact (eq_refl (@all _126408)). Qed.
Lemma lem6919102 {_126408 : Type'} : (term51 _126408) = (term46 _126408).
Proof. exact (MK_COMB (@lem6919101 _126408) (@lem6919100 _126408)). Qed.
Lemma lem6919103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6919104 {_126408 : Type'} : (term60 _126408) = (term61 _126408).
Proof. exact (MK_COMB (@lem6919103) (@lem6919102 _126408)). Qed.
Lemma lem6919105 {_126408 : Type'} (x : _126408) : (term54 _126408 x) = (term40 _126408 x).
Proof. exact (eq_refl (term54 _126408 x)). Qed.
Lemma lem6919106 {_126408 : Type'} (f : _126408 -> int) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6919107 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term55 _126408 x f) = (term56 _126408 x f).
Proof. exact (MK_COMB (@lem6919105 _126408 x) (@lem6919106 _126408 f)). Qed.
Lemma lem6919108 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term56 _126408 x f) = (term38 _126408 x f).
Proof. exact (eq_refl (term56 _126408 x f)). Qed.
Lemma lem6919109 {_126408 : Type'} (x : _126408) (f : _126408 -> int) : (term55 _126408 x f) = (term38 _126408 x f).
Proof. exact (TRANS (@lem6919107 _126408 x f) (@lem6919108 _126408 x f)). Qed.
Lemma lem6919110 {_126408 : Type'} (f : _126408 -> int) : (term62 _126408 f) = (term63 _126408 f).
Proof. exact (fun_ext (fun x : _126408 => @lem6919109 _126408 x f)). Qed.
Lemma lem6919111 {_126408 : Type'} : (@all _126408) = (@all _126408).
Proof. exact (eq_refl (@all _126408)). Qed.
Lemma lem6919112 {_126408 : Type'} (f : _126408 -> int) : (term64 _126408 f) = (term65 _126408 f).
Proof. exact (MK_COMB (@lem6919111 _126408) (@lem6919110 _126408 f)). Qed.
Lemma lem6919113 {_126408 : Type'} : (term66 _126408) = (term67 _126408).
Proof. exact (fun_ext (fun f : _126408 -> int => @lem6919112 _126408 f)). Qed.
Lemma lem6919114 {_126408 : Type'} : (@all (_126408 -> int)) = (@all (_126408 -> int)).
Proof. exact (eq_refl (@all (_126408 -> int))). Qed.
Lemma lem6919115 {_126408 : Type'} : (term52 _126408) = (term68 _126408).
Proof. exact (MK_COMB (@lem6919114 _126408) (@lem6919113 _126408)). Qed.
Lemma lem6919116 {_126408 : Type'} : ((term51 _126408) = (term52 _126408)) = ((term46 _126408) = (term68 _126408)).
Proof. exact (MK_COMB (@lem6919104 _126408) (@lem6919115 _126408)). Qed.
Lemma lem6919117 {_126408 : Type'} : (term46 _126408) = (term68 _126408).
Proof. exact (EQ_MP (@lem6919116 _126408) (@lem6919091 _126408)). Qed.
Lemma lem6919118 {_126367 : Type'} : (term17 _126367) = (term17 _126367).
Proof. exact (eq_refl (term17 _126367)). Qed.
Lemma lem6919119 {_126367 _126408 : Type'} : (term48 _126367 _126408) = (term69 _126367 _126408).
Proof. exact (MK_COMB (@lem6919118 _126367) (@lem6919117 _126408)). Qed.
Lemma lem6919120 {_126367 _126408 : Type'} : (term69 _126367 _126408) = (term48 _126367 _126408).
Proof. exact (SYM (@lem6919119 _126367 _126408)). Qed.
Lemma lem6919122 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term2 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6918962 _120477 _120519 _120521 op) (@lem6918961 _120477 _120519 _120521 op)). Qed.
Lemma lem6919123 {_126367 _126408 : Type'} (op : type1551) : term70 _126367 _126408 op.
Proof. exact (@lem6919122 _126367 int _126408 op). Qed.
Lemma lem6919124 {_126367 _126408 : Type'} : term71 _126367 _126408.
Proof. exact (@lem6919123 _126367 _126408 int_add). Qed.
Lemma lem6919126 : (@monoidal int int_add) = True.
Proof. exact (EQ_MP (@lem6918946) (@lem6918945)). Qed.
Lemma lem6919127 : True = (@monoidal int int_add).
Proof. exact (SYM (@lem6919126)). Qed.
Lemma lem6919128 : @monoidal int int_add.
Proof. exact (EQ_MP (@lem6919127) (@lem0)). Qed.
Lemma lem6919129 {_126367 _126408 : Type'} : term69 _126367 _126408.
Proof. exact (@lem6919124 _126367 _126408 (@lem6919128)). Qed.
Lemma lem6919130 {_126367 _126408 : Type'} : term48 _126367 _126408.
Proof. exact (EQ_MP (@lem6919120 _126367 _126408) (@lem6919129 _126367 _126408)). Qed.
Lemma lem6919131 {_126367 _126408 : Type'} : term47 _126367 _126408.
Proof. exact (EQ_MP (@lem6919079 _126367 _126408) (@lem6919130 _126367 _126408)). Qed.
