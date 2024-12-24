Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_DELTA_term_abbrevs.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_SING_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import SUPPORT_CLAUSES_spec.
Require Import SUPPORT_DELTA_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm15249_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5824998 {_120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term0 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5736505 Prop _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5825053 {_120011 _120196 : Type'} (op : type1400 _120196) : term1 _120011 _120196 op.
Proof. exact (proj1 (@lem5824998 _120011 Prop Prop Prop Prop Prop Prop _120196 op)). Qed.
Lemma lem5825054 {_120011 _120196 : Type'} (op : type1400 _120196) (f : _120011 -> _120196) : term2 _120011 _120196 op f.
Proof. exact (@lem5825053 _120011 _120196 op f). Qed.
Lemma lem5825055 {_120011 _120196 : Type'} (op : type1400 _120196) (f : _120011 -> _120196) : (term2 _120011 _120196 op f) = (term3 _120011 _120196 op f).
Proof. exact (eq_refl (term2 _120011 _120196 op f)). Qed.
Lemma lem5825056 {_120011 _120196 : Type'} (op : type1400 _120196) (f : _120011 -> _120196) : term3 _120011 _120196 op f.
Proof. exact (EQ_MP (@lem5825055 _120011 _120196 op f) (@lem5825054 _120011 _120196 op f)). Qed.
Lemma lem5825057 {_120011 _120196 : Type'} (op : type1400 _120196) (f : _120011 -> _120196) (x : _120011) : term4 _120011 _120196 op f x.
Proof. exact (@lem5825056 _120011 _120196 op f x). Qed.
Lemma lem5825058 {_120011 _120196 : Type'} (x : _120011) (op : type1400 _120196) (f : _120011 -> _120196) : (term4 _120011 _120196 op f x) = (term5 _120011 _120196 x op f).
Proof. exact (eq_refl (term4 _120011 _120196 op f x)). Qed.
Lemma lem5825059 {_120011 _120196 : Type'} (x : _120011) (op : type1400 _120196) (f : _120011 -> _120196) : term5 _120011 _120196 x op f.
Proof. exact (EQ_MP (@lem5825058 _120011 _120196 x op f) (@lem5825057 _120011 _120196 op f x)). Qed.
Lemma lem5825060 {_120011 _120196 : Type'} (x : _120011) (op : type1400 _120196) (f : _120011 -> _120196) (s : _120011 -> Prop) : term6 _120011 _120196 x op f s.
Proof. exact (@lem5825059 _120011 _120196 x op f s). Qed.
Lemma lem5825061 {_120011 _120196 : Type'} (x : _120011) (op : type1400 _120196) (f : _120011 -> _120196) (s : _120011 -> Prop) : (term6 _120011 _120196 x op f s) = ((term7 _120011 _120196 op f x s) = (term8 _120011 _120196 x op f s)).
Proof. exact (eq_refl (term6 _120011 _120196 x op f s)). Qed.
Lemma lem5825063 {_119963 _120196 : Type'} (op : type1400 _120196) : term9 _119963 _120196 op.
Proof. exact (proj1 (@lem5736505 _119963 Prop Prop Prop Prop Prop Prop Prop _120196 op)). Qed.
Lemma lem5825064 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : term10 _119963 _120196 op f.
Proof. exact (@lem5825063 _119963 _120196 op f). Qed.
Lemma lem5825065 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : (term10 _119963 _120196 op f) = ((@support _119963 _120196 op f (@EMPTY _119963)) = (@EMPTY _119963)).
Proof. exact (eq_refl (term10 _119963 _120196 op f)). Qed.
Lemma lem5825067 {_120222 _120250 : Type'} (op : type1400 _120222) : term11 _120222 _120250 op.
Proof. exact (@lem5737458 _120222 _120250 op). Qed.
Lemma lem5825068 {_120222 _120250 : Type'} (op : type1400 _120222) : (term11 _120222 _120250 op) = (term12 _120222 _120250 op).
Proof. exact (eq_refl (term11 _120222 _120250 op)). Qed.
Lemma lem5825069 {_120222 _120250 : Type'} (op : type1400 _120222) : term12 _120222 _120250 op.
Proof. exact (EQ_MP (@lem5825068 _120222 _120250 op) (@lem5825067 _120222 _120250 op)). Qed.
Lemma lem5825070 {_120222 _120250 : Type'} (op : type1400 _120222) (s : _120250 -> Prop) : term13 _120222 _120250 op s.
Proof. exact (@lem5825069 _120222 _120250 op s). Qed.
Lemma lem5825071 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) : (term13 _120222 _120250 op s) = (term14 _120222 _120250 s op).
Proof. exact (eq_refl (term13 _120222 _120250 op s)). Qed.
Lemma lem5825072 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) : term14 _120222 _120250 s op.
Proof. exact (EQ_MP (@lem5825071 _120222 _120250 s op) (@lem5825070 _120222 _120250 op s)). Qed.
Lemma lem5825073 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) : term15 _120222 _120250 s op f.
Proof. exact (@lem5825072 _120222 _120250 s op f). Qed.
Lemma lem5825074 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) : (term15 _120222 _120250 s op f) = (term16 _120222 _120250 s op f).
Proof. exact (eq_refl (term15 _120222 _120250 s op f)). Qed.
Lemma lem5825075 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) : term16 _120222 _120250 s op f.
Proof. exact (EQ_MP (@lem5825074 _120222 _120250 s op f) (@lem5825073 _120222 _120250 s op f)). Qed.
Lemma lem5825076 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) (a : _120250) : term17 _120222 _120250 s op f a.
Proof. exact (@lem5825075 _120222 _120250 s op f a). Qed.
Lemma lem5825077 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) (a : _120250) : (term17 _120222 _120250 s op f a) = ((term18 _120222 _120250 a f op s) = (term19 _120222 _120250 s op f a)).
Proof. exact (eq_refl (term17 _120222 _120250 s op f a)). Qed.
Lemma lem5825082 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term20 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term20 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5825083 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term20 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f).
Proof. exact (SYM (@lem5825082 _120296 _120308 op s f h1)). Qed.
Lemma lem5825084 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5825085 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f)) : (term20 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem5825084 _120296 _120308 op s f h1)). Qed.
Lemma lem5825086 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term20 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term20 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem5825083 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f) => @lem5825085 _120296 _120308 op s f h1)). Qed.
Lemma lem5825087 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term21 _120296 _120308 op f) = (term22 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5825086 _120296 _120308 op s f)). Qed.
Lemma lem5825088 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5825089 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term23 _120296 _120308 op f) = (term24 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem5825088 _120308) (@lem5825087 _120296 _120308 op f)). Qed.
Lemma lem5825090 {_120296 _120308 : Type'} (op : type1400 _120296) : (term25 _120296 _120308 op) = (term26 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem5825089 _120296 _120308 op f)). Qed.
Lemma lem5825091 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem5825092 {_120296 _120308 : Type'} (op : type1400 _120296) : (term27 _120296 _120308 op) = (term28 _120296 _120308 op).
Proof. exact (MK_COMB (@lem5825091 _120296 _120308) (@lem5825090 _120296 _120308 op)). Qed.
Lemma lem5825093 {_120296 _120308 : Type'} : (term29 _120296 _120308) = (term30 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem5825092 _120296 _120308 op)). Qed.
Lemma lem5825094 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem5825095 {_120296 _120308 : Type'} : (term31 _120296 _120308) = (term32 _120296 _120308).
Proof. exact (MK_COMB (@lem5825094 _120296) (@lem5825093 _120296 _120308)). Qed.
Lemma lem5825096 {_120296 _120308 : Type'} : term32 _120296 _120308.
Proof. exact (EQ_MP (@lem5825095 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem5825097 {_120296 _120308 : Type'} (op : type1400 _120296) : term33 _120296 _120308 op.
Proof. exact (@lem5825096 _120296 _120308 op). Qed.
Lemma lem5825098 {_120296 _120308 : Type'} (op : type1400 _120296) : (term33 _120296 _120308 op) = (term28 _120296 _120308 op).
Proof. exact (eq_refl (term33 _120296 _120308 op)). Qed.
Lemma lem5825099 {_120296 _120308 : Type'} (op : type1400 _120296) : term28 _120296 _120308 op.
Proof. exact (EQ_MP (@lem5825098 _120296 _120308 op) (@lem5825097 _120296 _120308 op)). Qed.
Lemma lem5825100 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term34 _120296 _120308 op f.
Proof. exact (@lem5825099 _120296 _120308 op f). Qed.
Lemma lem5825101 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term34 _120296 _120308 op f) = (term24 _120296 _120308 op f).
Proof. exact (eq_refl (term34 _120296 _120308 op f)). Qed.
Lemma lem5825102 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term24 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem5825101 _120296 _120308 op f) (@lem5825100 _120296 _120308 op f)). Qed.
Lemma lem5825103 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term35 _120296 _120308 op f s.
Proof. exact (@lem5825102 _120296 _120308 op f s). Qed.
Lemma lem5825104 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term35 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f)).
Proof. exact (eq_refl (term35 _120296 _120308 op f s)). Qed.
Lemma lem5825106 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : @monoidal _121513 op.
Proof. exact (h1). Qed.
Lemma lem5825122 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term20 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5825104 _120296 _120308 op s f) (@lem5825103 _120296 _120308 op f s)). Qed.
Lemma lem5825123 {_121513 _121532 : Type'} (op : type1400 _121513) (s : _121532 -> Prop) (f : _121532 -> _121513) : (@iterate _121513 _121532 op s f) = (term20 _121513 _121532 op s f).
Proof. exact (@lem5825122 _121513 _121532 op s f). Qed.
Lemma lem5825124 {_121513 _121532 : Type'} (s : _121532 -> Prop) (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) : (term36 _121513 _121532 s a f op) = (term37 _121513 _121532 s a f op).
Proof. exact (@lem5825123 _121513 _121532 op s (term38 _121513 _121532 a f op)). Qed.
Lemma lem5825125 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825126 {_121513 _121532 : Type'} (s : _121532 -> Prop) (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) : (term39 _121513 _121532 s a f op) = (term40 _121513 _121532 s a f op).
Proof. exact (MK_COMB (@lem5825125 _121513) (@lem5825124 _121513 _121532 s a f op)). Qed.
Lemma lem5825127 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term41 _121513 _121532 s f a op) = (term41 _121513 _121532 s f a op).
Proof. exact (eq_refl (term41 _121513 _121532 s f a op)). Qed.
Lemma lem5825128 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term36 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)) = ((term37 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (MK_COMB (@lem5825126 _121513 _121532 s a f op) (@lem5825127 _121513 _121532 s f a op)). Qed.
Lemma lem5825129 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term42 _121513 _121532 f a op) = (term43 _121513 _121532 f a op).
Proof. exact (fun_ext (fun s : _121532 -> Prop => @lem5825128 _121513 _121532 s f a op)). Qed.
Lemma lem5825130 {_121532 : Type'} : (@all (_121532 -> Prop)) = (@all (_121532 -> Prop)).
Proof. exact (eq_refl (@all (_121532 -> Prop))). Qed.
Lemma lem5825131 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term44 _121513 _121532 f a op) = (term45 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825130 _121532) (@lem5825129 _121513 _121532 f a op)). Qed.
Lemma lem5825132 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : (term46 _121513 _121532 f op) = (term47 _121513 _121532 f op).
Proof. exact (fun_ext (fun a : _121532 => @lem5825131 _121513 _121532 f a op)). Qed.
Lemma lem5825133 {_121532 : Type'} : (@all _121532) = (@all _121532).
Proof. exact (eq_refl (@all _121532)). Qed.
Lemma lem5825134 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : (term48 _121513 _121532 f op) = (term49 _121513 _121532 f op).
Proof. exact (MK_COMB (@lem5825133 _121532) (@lem5825132 _121513 _121532 f op)). Qed.
Lemma lem5825135 {_121513 _121532 : Type'} (op : type1400 _121513) : (term50 _121513 _121532 op) = (term51 _121513 _121532 op).
Proof. exact (fun_ext (fun f : _121532 -> _121513 => @lem5825134 _121513 _121532 f op)). Qed.
Lemma lem5825136 {_121513 _121532 : Type'} : (@all (_121532 -> _121513)) = (@all (_121532 -> _121513)).
Proof. exact (eq_refl (@all (_121532 -> _121513))). Qed.
Lemma lem5825137 {_121513 _121532 : Type'} (op : type1400 _121513) : (term52 _121513 _121532 op) = (term53 _121513 _121532 op).
Proof. exact (MK_COMB (@lem5825136 _121513 _121532) (@lem5825135 _121513 _121532 op)). Qed.
Lemma lem5825138 {_121513 _121532 : Type'} (op : type1400 _121513) : (term53 _121513 _121532 op) = (term52 _121513 _121532 op).
Proof. exact (SYM (@lem5825137 _121513 _121532 op)). Qed.
Lemma lem5825154 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) (a : _120250) : (term18 _120222 _120250 a f op s) = (term19 _120222 _120250 s op f a).
Proof. exact (EQ_MP (@lem5825077 _120222 _120250 s op f a) (@lem5825076 _120222 _120250 s op f a)). Qed.
Lemma lem5825155 {_121513 _121532 : Type'} (s : _121532 -> Prop) (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term18 _121513 _121532 a f op s) = (term19 _121513 _121532 s op f a).
Proof. exact (@lem5825154 _121513 _121532 s op f a). Qed.
Lemma lem5825156 {_121513 _121532 : Type'} (op : type1400 _121513) : (@iterate _121513 _121532 op) = (@iterate _121513 _121532 op).
Proof. exact (eq_refl (@iterate _121513 _121532 op)). Qed.
Lemma lem5825157 {_121513 _121532 : Type'} (s : _121532 -> Prop) (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term54 _121513 _121532 a f op s) = (term55 _121513 _121532 s op f a).
Proof. exact (MK_COMB (@lem5825156 _121513 _121532 op) (@lem5825155 _121513 _121532 s op f a)). Qed.
Lemma lem5825162 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) : (term38 _121513 _121532 a f op) = (term38 _121513 _121532 a f op).
Proof. exact (eq_refl (term38 _121513 _121532 a f op)). Qed.
Lemma lem5825163 {_121513 _121532 : Type'} (s : _121532 -> Prop) (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) : (term37 _121513 _121532 s a f op) = (term56 _121513 _121532 s a f op).
Proof. exact (MK_COMB (@lem5825157 _121513 _121532 s op f a) (@lem5825162 _121513 _121532 a f op)). Qed.
Lemma lem5825164 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825165 {_121513 _121532 : Type'} (s : _121532 -> Prop) (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) : (term40 _121513 _121532 s a f op) = (term57 _121513 _121532 s a f op).
Proof. exact (MK_COMB (@lem5825164 _121513) (@lem5825163 _121513 _121532 s a f op)). Qed.
Lemma lem5825166 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term41 _121513 _121532 s f a op) = (term41 _121513 _121532 s f a op).
Proof. exact (eq_refl (term41 _121513 _121532 s f a op)). Qed.
Lemma lem5825167 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term37 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)) = ((term56 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (MK_COMB (@lem5825165 _121513 _121532 s a f op) (@lem5825166 _121513 _121532 s f a op)). Qed.
Lemma lem5825170 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term43 _121513 _121532 f a op) = (term58 _121513 _121532 f a op).
Proof. exact (fun_ext (fun s : _121532 -> Prop => @lem5825167 _121513 _121532 s f a op)). Qed.
Lemma lem5825171 {_121532 : Type'} : (@all (_121532 -> Prop)) = (@all (_121532 -> Prop)).
Proof. exact (eq_refl (@all (_121532 -> Prop))). Qed.
Lemma lem5825172 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term45 _121513 _121532 f a op) = (term59 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825171 _121532) (@lem5825170 _121513 _121532 f a op)). Qed.
Lemma lem5825177 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : (term47 _121513 _121532 f op) = (term60 _121513 _121532 f op).
Proof. exact (fun_ext (fun a : _121532 => @lem5825172 _121513 _121532 f a op)). Qed.
Lemma lem5825178 {_121532 : Type'} : (@all _121532) = (@all _121532).
Proof. exact (eq_refl (@all _121532)). Qed.
Lemma lem5825179 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : (term49 _121513 _121532 f op) = (term61 _121513 _121532 f op).
Proof. exact (MK_COMB (@lem5825178 _121532) (@lem5825177 _121513 _121532 f op)). Qed.
Lemma lem5825184 {_121513 _121532 : Type'} (op : type1400 _121513) : (term51 _121513 _121532 op) = (term62 _121513 _121532 op).
Proof. exact (fun_ext (fun f : _121532 -> _121513 => @lem5825179 _121513 _121532 f op)). Qed.
Lemma lem5825185 {_121513 _121532 : Type'} : (@all (_121532 -> _121513)) = (@all (_121532 -> _121513)).
Proof. exact (eq_refl (@all (_121532 -> _121513))). Qed.
Lemma lem5825186 {_121513 _121532 : Type'} (op : type1400 _121513) : (term53 _121513 _121532 op) = (term63 _121513 _121532 op).
Proof. exact (MK_COMB (@lem5825185 _121513 _121532) (@lem5825184 _121513 _121532 op)). Qed.
Lemma lem5825191 {_121513 _121532 : Type'} (op : type1400 _121513) : (term63 _121513 _121532 op) = (term53 _121513 _121532 op).
Proof. exact (SYM (@lem5825186 _121513 _121532 op)). Qed.
Lemma lem5825192 {_121532 : Type'} (_474 : _121532 -> Prop) (_475 : Prop) (_476 : type686 _121532) (_477 : _121532 -> Prop) : (term64 _121532 _476 _475 _474 _477) = (term65 _121532 _474 _475 _476 _477).
Proof. exact (@lem13473 (_121532 -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5825193 {_121513 _121532 : Type'} (_474 : _121532 -> Prop) (_475 : Prop) (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (_477 : _121532 -> Prop) : (term66 _121513 _121532 s f a op _475 _474 _477) = (term67 _121513 _121532 _474 _475 s f a op _477).
Proof. exact (@lem5825192 _121532 _474 _475 (term68 _121513 _121532 s f a op) _477). Qed.
Lemma lem5825194 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term69 _121513 _121532 s op f a) = (term70 _121513 _121532 s f a op).
Proof. exact (@lem5825193 _121513 _121532 (term71 _121513 _121532 op f a) (@IN _121532 a s) s f a op (@EMPTY _121532)). Qed.
Lemma lem5825195 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term72 _121513 _121532 s f a op) = ((term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (eq_refl (term72 _121513 _121532 s f a op)). Qed.
Lemma lem5825196 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) : (term74 _121532 a s) = (term74 _121532 a s).
Proof. exact (eq_refl (term74 _121532 a s)). Qed.
Lemma lem5825197 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term75 _121513 _121532 s f a op) = (term76 _121513 _121532 s f a op).
Proof. exact (MK_COMB (@lem5825196 _121532 a s) (@lem5825195 _121513 _121532 s f a op)). Qed.
Lemma lem5825198 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term77 _121513 _121532 s op f a) = ((term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (eq_refl (term77 _121513 _121532 s op f a)). Qed.
Lemma lem5825199 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) : (term79 _121532 a s) = (term79 _121532 a s).
Proof. exact (eq_refl (term79 _121532 a s)). Qed.
Lemma lem5825200 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term80 _121513 _121532 s op f a) = (term81 _121513 _121532 s f a op).
Proof. exact (MK_COMB (@lem5825199 _121532 a s) (@lem5825198 _121513 _121532 s f a op)). Qed.
Lemma lem5825201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5825202 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term82 _121513 _121532 s op f a) = (term83 _121513 _121532 s f a op).
Proof. exact (MK_COMB (@lem5825201) (@lem5825200 _121513 _121532 s f a op)). Qed.
Lemma lem5825203 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term70 _121513 _121532 s f a op) = (term84 _121513 _121532 s f a op).
Proof. exact (MK_COMB (@lem5825202 _121513 _121532 s f a op) (@lem5825197 _121513 _121532 s f a op)). Qed.
Lemma lem5825204 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term69 _121513 _121532 s op f a) = ((term56 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (eq_refl (term69 _121513 _121532 s op f a)). Qed.
Lemma lem5825205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5825206 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term85 _121513 _121532 s op f a) = (term86 _121513 _121532 s f a op).
Proof. exact (MK_COMB (@lem5825205) (@lem5825204 _121513 _121532 s f a op)). Qed.
Lemma lem5825207 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term69 _121513 _121532 s op f a) = (term70 _121513 _121532 s f a op)) = (((term56 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)) = (term84 _121513 _121532 s f a op)).
Proof. exact (MK_COMB (@lem5825206 _121513 _121532 s f a op) (@lem5825203 _121513 _121532 s f a op)). Qed.
Lemma lem5825208 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term56 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)) = (term84 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem5825207 _121513 _121532 s f a op) (@lem5825194 _121513 _121532 s f a op)). Qed.
Lemma lem5825209 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term84 _121513 _121532 s f a op) = ((term56 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (SYM (@lem5825208 _121513 _121532 s f a op)). Qed.
Lemma lem5825210 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) (h1 : @IN _121532 a s) : @IN _121532 a s.
Proof. exact (h1). Qed.
Lemma lem5825211 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) : (@IN _121532 a s) = ((@IN _121532 a s) = True).
Proof. exact (@lem7 (@IN _121532 a s)). Qed.
Lemma lem5825212 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) (h1 : @IN _121532 a s) : (@IN _121532 a s) = True.
Proof. exact (EQ_MP (@lem5825211 _121532 a s) (@lem5825210 _121532 a s h1)). Qed.
Lemma lem5825213 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term87 _121513 _121532 f a op) = (term87 _121513 _121532 f a op).
Proof. exact (eq_refl (term87 _121513 _121532 f a op)). Qed.
Lemma lem5825214 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @IN _121532 a s) : (term88 _121513 _121532 f op a s) = (term89 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825213 _121513 _121532 f a op) (@lem5825212 _121532 a s h1)). Qed.
Lemma lem5825215 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term89 _121513 _121532 f a op) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op)).
Proof. exact (eq_refl (term89 _121513 _121532 f a op)). Qed.
Lemma lem5825216 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) : (term91 _121513 _121532 f op a s) = (term91 _121513 _121532 f op a s).
Proof. exact (eq_refl (term91 _121513 _121532 f op a s)). Qed.
Lemma lem5825217 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term88 _121513 _121532 f op a s) = (term89 _121513 _121532 f a op)) = ((term88 _121513 _121532 f op a s) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op))).
Proof. exact (MK_COMB (@lem5825216 _121513 _121532 f op a s) (@lem5825215 _121513 _121532 f a op)). Qed.
Lemma lem5825218 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term88 _121513 _121532 f op a s) = ((term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (eq_refl (term88 _121513 _121532 f op a s)). Qed.
Lemma lem5825219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5825220 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term91 _121513 _121532 f op a s) = (term92 _121513 _121532 s f a op).
Proof. exact (MK_COMB (@lem5825219) (@lem5825218 _121513 _121532 s f a op)). Qed.
Lemma lem5825221 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op)) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op)).
Proof. exact (eq_refl ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op))). Qed.
Lemma lem5825222 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term88 _121513 _121532 f op a s) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op))) = (((term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op))).
Proof. exact (MK_COMB (@lem5825220 _121513 _121532 s f a op) (@lem5825221 _121513 _121532 f a op)). Qed.
Lemma lem5825223 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term88 _121513 _121532 f op a s) = (term89 _121513 _121532 f a op)) = (((term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op))).
Proof. exact (TRANS (@lem5825217 _121513 _121532 s f a op) (@lem5825222 _121513 _121532 s f a op)). Qed.
Lemma lem5825224 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @IN _121532 a s) : ((term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op)).
Proof. exact (EQ_MP (@lem5825223 _121513 _121532 s f a op) (@lem5825214 _121513 _121532 f op a s h1)). Qed.
Lemma lem5825225 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @IN _121532 a s) : ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op)) = ((term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (SYM (@lem5825224 _121513 _121532 f op a s h1)). Qed.
Lemma lem5825226 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) (h1 : term93 _121532 a s) : term93 _121532 a s.
Proof. exact (h1). Qed.
Lemma lem5825227 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) : term94 _121532 a s.
Proof. exact (@lem82 (@IN _121532 a s)). Qed.
Lemma lem5825228 {_121532 : Type'} (a : _121532) (s : _121532 -> Prop) (h1 : term93 _121532 a s) : (@IN _121532 a s) = False.
Proof. exact (@lem5825227 _121532 a s (@lem5825226 _121532 a s h1)). Qed.
Lemma lem5825229 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term95 _121513 _121532 f a op) = (term95 _121513 _121532 f a op).
Proof. exact (eq_refl (term95 _121513 _121532 f a op)). Qed.
Lemma lem5825230 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : term93 _121532 a s) : (term96 _121513 _121532 f op a s) = (term97 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825229 _121513 _121532 f a op) (@lem5825228 _121532 a s h1)). Qed.
Lemma lem5825231 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term97 _121513 _121532 f a op) = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)).
Proof. exact (eq_refl (term97 _121513 _121532 f a op)). Qed.
Lemma lem5825232 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) : (term99 _121513 _121532 f op a s) = (term99 _121513 _121532 f op a s).
Proof. exact (eq_refl (term99 _121513 _121532 f op a s)). Qed.
Lemma lem5825233 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term96 _121513 _121532 f op a s) = (term97 _121513 _121532 f a op)) = ((term96 _121513 _121532 f op a s) = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op))).
Proof. exact (MK_COMB (@lem5825232 _121513 _121532 f op a s) (@lem5825231 _121513 _121532 f a op)). Qed.
Lemma lem5825234 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term96 _121513 _121532 f op a s) = ((term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (eq_refl (term96 _121513 _121532 f op a s)). Qed.
Lemma lem5825235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5825236 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term99 _121513 _121532 f op a s) = (term100 _121513 _121532 s f a op).
Proof. exact (MK_COMB (@lem5825235) (@lem5825234 _121513 _121532 s f a op)). Qed.
Lemma lem5825237 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)) = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)).
Proof. exact (eq_refl ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op))). Qed.
Lemma lem5825238 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term96 _121513 _121532 f op a s) = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op))) = (((term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)) = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op))).
Proof. exact (MK_COMB (@lem5825236 _121513 _121532 s f a op) (@lem5825237 _121513 _121532 f a op)). Qed.
Lemma lem5825239 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term96 _121513 _121532 f op a s) = (term97 _121513 _121532 f a op)) = (((term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)) = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op))).
Proof. exact (TRANS (@lem5825233 _121513 _121532 s f a op) (@lem5825238 _121513 _121532 s f a op)). Qed.
Lemma lem5825240 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : term93 _121532 a s) : ((term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)) = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)).
Proof. exact (EQ_MP (@lem5825239 _121513 _121532 s f a op) (@lem5825230 _121513 _121532 f op a s h1)). Qed.
Lemma lem5825241 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : term93 _121532 a s) : ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)) = ((term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (SYM (@lem5825240 _121513 _121532 f op a s h1)). Qed.
Lemma lem5825287 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term101 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5825288 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term102 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5825287 _2963 g t e g' t' e'). Qed.
Lemma lem5825289 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term103 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5825288 _2963 g t e g' t'). Qed.
Lemma lem5825290 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term104 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5825289 _2963 g t e g'). Qed.
Lemma lem5825291 {_121513 : Type'} (g : Prop) (t : _121513) (e : _121513) : term104 _121513 g t e.
Proof. exact (@lem5825290 _121513 g t e). Qed.
Lemma lem5825292 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) : term105 _121513 _121532 a f x op.
Proof. exact (@lem5825291 _121513 (x = a) (f x) (@neutral _121513 op)). Qed.
Lemma lem5825293 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) : term106 _121513 _121532 a f x op g'.
Proof. exact (@lem5825292 _121513 _121532 a f x op g'). Qed.
Lemma lem5825294 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) : (term106 _121513 _121532 a f x op g') = (term107 _121513 _121532 a f x op g').
Proof. exact (eq_refl (term106 _121513 _121532 a f x op g')). Qed.
Lemma lem5825295 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) : term107 _121513 _121532 a f x op g'.
Proof. exact (EQ_MP (@lem5825294 _121513 _121532 a f x op g') (@lem5825293 _121513 _121532 a f x op g')). Qed.
Lemma lem5825296 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) (t' : _121513) : term108 _121513 _121532 a f x op g' t'.
Proof. exact (@lem5825295 _121513 _121532 a f x op g' t'). Qed.
Lemma lem5825297 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) (t' : _121513) : (term108 _121513 _121532 a f x op g' t') = (term109 _121513 _121532 a f x op g' t').
Proof. exact (eq_refl (term108 _121513 _121532 a f x op g' t')). Qed.
Lemma lem5825298 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) (t' : _121513) : term109 _121513 _121532 a f x op g' t'.
Proof. exact (EQ_MP (@lem5825297 _121513 _121532 a f x op g' t') (@lem5825296 _121513 _121532 a f x op g' t')). Qed.
Lemma lem5825299 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) (t' : _121513) (e' : _121513) : term110 _121513 _121532 a f x op g' t' e'.
Proof. exact (@lem5825298 _121513 _121532 a f x op g' t' e'). Qed.
Lemma lem5825300 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) (t' : _121513) (e' : _121513) : (term110 _121513 _121532 a f x op g' t' e') = (term111 _121513 _121532 a f x op g' t' e').
Proof. exact (eq_refl (term110 _121513 _121532 a f x op g' t' e')). Qed.
Lemma lem5825301 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (x : _121532) (op : type1400 _121513) (g' : Prop) (t' : _121513) (e' : _121513) : term111 _121513 _121532 a f x op g' t' e'.
Proof. exact (EQ_MP (@lem5825300 _121513 _121532 a f x op g' t' e') (@lem5825299 _121513 _121532 a f x op g' t' e')). Qed.
Lemma lem5825304 {_121532 : Type'} (x : _121532) (a : _121532) : (x = a) = (x = a).
Proof. exact (eq_refl (x = a)). Qed.
Lemma lem5825305 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (x : _121532) (a : _121532) (t' : _121513) (e' : _121513) : term112 _121513 _121532 f op x a t' e'.
Proof. exact (@lem5825301 _121513 _121532 a f x op (x = a) t' e'). Qed.
Lemma lem5825306 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (x : _121532) (a : _121532) (t' : _121513) (e' : _121513) : term113 _121513 _121532 f op x a t' e'.
Proof. exact (@lem5825305 _121513 _121532 f op x a t' e' (@lem5825304 _121532 x a)). Qed.
Lemma lem5825309 {_121532 : Type'} (x : _121532) (a : _121532) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5825310 {_121513 _121532 : Type'} (f : _121532 -> _121513) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5825311 {_121513 _121532 : Type'} (f : _121532 -> _121513) (x : _121532) (a : _121532) (h1 : x = a) : (f x) = (f a).
Proof. exact (MK_COMB (@lem5825310 _121513 _121532 f) (@lem5825309 _121532 x a h1)). Qed.
Lemma lem5825312 {_121513 _121532 : Type'} (x : _121532) (f : _121532 -> _121513) (a : _121532) : term114 _121513 _121532 x f a.
Proof. exact (fun h0 : x = a => @lem5825311 _121513 _121532 f x a h0). Qed.
Lemma lem5825313 {_121513 _121532 : Type'} (op : type1400 _121513) (x : _121532) (f : _121532 -> _121513) (a : _121532) (e' : _121513) : term115 _121513 _121532 op x f a e'.
Proof. exact (@lem5825306 _121513 _121532 f op x a (f a) e'). Qed.
Lemma lem5825314 {_121513 _121532 : Type'} (op : type1400 _121513) (x : _121532) (f : _121532 -> _121513) (a : _121532) (e' : _121513) : term116 _121513 _121532 op x f a e'.
Proof. exact (@lem5825313 _121513 _121532 op x f a e' (@lem5825312 _121513 _121532 x f a)). Qed.
Lemma lem5825329 {_121513 : Type'} (op : type1400 _121513) : (@neutral _121513 op) = (@neutral _121513 op).
Proof. exact (eq_refl (@neutral _121513 op)). Qed.
Lemma lem5825330 {_121513 _121532 : Type'} (x : _121532) (a : _121532) (op : type1400 _121513) : term117 _121513 _121532 x a op.
Proof. exact (fun h0 : term118 _121532 x a => @lem5825329 _121513 op). Qed.
Lemma lem5825331 {_121513 _121532 : Type'} (x : _121532) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : term119 _121513 _121532 x f a op.
Proof. exact (@lem5825314 _121513 _121532 op x f a (@neutral _121513 op)). Qed.
Lemma lem5825332 {_121513 _121532 : Type'} (x : _121532) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term120 _121513 _121532 a f x op) = (term121 _121513 _121532 x f a op).
Proof. exact (@lem5825331 _121513 _121532 x f a op (@lem5825330 _121513 _121532 x a op)). Qed.
Lemma lem5825381 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term38 _121513 _121532 a f op) = (term122 _121513 _121532 f a op).
Proof. exact (fun_ext (fun x : _121532 => @lem5825332 _121513 _121532 x f a op)). Qed.
Lemma lem5825430 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term123 _121513 _121532 op f a) = (term123 _121513 _121532 op f a).
Proof. exact (eq_refl (term123 _121513 _121532 op f a)). Qed.
Lemma lem5825431 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term78 _121513 _121532 a f op) = (term124 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825430 _121513 _121532 op f a) (@lem5825381 _121513 _121532 f a op)). Qed.
Lemma lem5825480 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825481 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term125 _121513 _121532 a f op) = (term126 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825480 _121513) (@lem5825431 _121513 _121532 f a op)). Qed.
Lemma lem5825531 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5825532 {_121513 : Type'} (t2 : _121513) (t1 : _121513) : (@COND _121513 True t1 t2) = t1.
Proof. exact (@lem5825531 _121513 t2 t1). Qed.
Lemma lem5825533 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term90 _121513 _121532 f a op) = (f a).
Proof. exact (@lem5825532 _121513 (@neutral _121513 op) (f a)). Qed.
Lemma lem5825534 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op)) = ((term124 _121513 _121532 f a op) = (f a)).
Proof. exact (MK_COMB (@lem5825481 _121513 _121532 f a op) (@lem5825533 _121513 _121532 op f a)). Qed.
Lemma lem5825585 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term124 _121513 _121532 f a op) = (f a)) = ((term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op)).
Proof. exact (SYM (@lem5825534 _121513 _121532 op f a)). Qed.
Lemma lem5825586 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term127 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5825587 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term127 _120477 _120519 _120521 op) = (term128 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term127 _120477 _120519 _120521 op)). Qed.
Lemma lem5825588 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term128 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5825587 _120477 _120519 _120521 op) (@lem5825586 _120477 _120519 _120521 op)). Qed.
Lemma lem5825589 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5825590 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term129 _120477 _120519 _120521 op.
Proof. exact (@lem5825588 _120477 _120519 _120521 op (@lem5825589 _120519 op h1)). Qed.
Lemma lem5825613 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term130 _120477 _120519 op.
Proof. exact (proj1 (@lem5825590 _120477 _120519 Prop op h1)). Qed.
Lemma lem5825614 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term131 _120477 _120519 op f.
Proof. exact (@lem5825613 _120477 _120519 op h1 f). Qed.
Lemma lem5825615 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term131 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term131 _120477 _120519 op f)). Qed.
Lemma lem5825616 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5825615 _120477 _120519 f op) (@lem5825614 _120477 _120519 f op h1)). Qed.
Lemma lem5825622 {_121513 : Type'} (op : type1400 _121513) : (@monoidal _121513 op) = ((@monoidal _121513 op) = True).
Proof. exact (@lem7 (@monoidal _121513 op)). Qed.
Lemma lem5825629 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term132 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5825616 _120477 _120519 f op h0). Qed.
Lemma lem5825630 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : term133 _121513 _121532 f op.
Proof. exact (@lem5825629 _121532 _121513 f op). Qed.
Lemma lem5825631 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) : term134 _121513 _121532 a f op.
Proof. exact (@lem5825630 _121513 _121532 (term38 _121513 _121532 a f op) op). Qed.
Lemma lem5825633 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : (@monoidal _121513 op) = True.
Proof. exact (EQ_MP (@lem5825622 _121513 op) (@lem5825106 _121513 op h1)). Qed.
Lemma lem5825634 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : True = (@monoidal _121513 op).
Proof. exact (SYM (@lem5825633 _121513 op h1)). Qed.
Lemma lem5825635 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : @monoidal _121513 op.
Proof. exact (EQ_MP (@lem5825634 _121513 op h1) (@lem0)). Qed.
Lemma lem5825636 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term73 _121513 _121532 a f op) = (@neutral _121513 op).
Proof. exact (@lem5825631 _121513 _121532 a f op (@lem5825635 _121513 op h1)). Qed.
Lemma lem5825637 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825638 {_121513 _121532 : Type'} (a : _121532) (f : _121532 -> _121513) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term135 _121513 _121532 a f op) = (term136 _121513 op).
Proof. exact (MK_COMB (@lem5825637 _121513) (@lem5825636 _121513 _121532 a f op h1)). Qed.
Lemma lem5825640 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5825641 {_121513 : Type'} (t1 : _121513) (t2 : _121513) : (@COND _121513 False t1 t2) = t2.
Proof. exact (@lem5825640 _121513 t1 t2). Qed.
Lemma lem5825642 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term98 _121513 _121532 f a op) = (@neutral _121513 op).
Proof. exact (@lem5825641 _121513 (f a) (@neutral _121513 op)). Qed.
Lemma lem5825643 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)) = ((@neutral _121513 op) = (@neutral _121513 op)).
Proof. exact (MK_COMB (@lem5825638 _121513 _121532 a f op h1) (@lem5825642 _121513 _121532 f a op)). Qed.
Lemma lem5825645 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5825646 {_121513 : Type'} (x : _121513) : (x = x) = True.
Proof. exact (@lem5825645 _121513 x). Qed.
Lemma lem5825647 {_121513 : Type'} (op : type1400 _121513) : ((@neutral _121513 op) = (@neutral _121513 op)) = True.
Proof. exact (@lem5825646 _121513 (@neutral _121513 op)). Qed.
Lemma lem5825648 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)) = True.
Proof. exact (TRANS (@lem5825643 _121513 _121532 f a op h1) (@lem5825647 _121513 op)). Qed.
Lemma lem5825649 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : True = ((term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op)).
Proof. exact (SYM (@lem5825648 _121513 _121532 f a op h1)). Qed.
Lemma lem5825650 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term73 _121513 _121532 a f op) = (term98 _121513 _121532 f a op).
Proof. exact (EQ_MP (@lem5825649 _121513 _121532 f a op h1) (@lem0)). Qed.
Lemma lem5825654 {_120011 _120196 : Type'} (x : _120011) (op : type1400 _120196) (f : _120011 -> _120196) (s : _120011 -> Prop) : (term7 _120011 _120196 op f x s) = (term8 _120011 _120196 x op f s).
Proof. exact (EQ_MP (@lem5825061 _120011 _120196 x op f s) (@lem5825060 _120011 _120196 x op f s)). Qed.
Lemma lem5825655 {_121513 _121532 : Type'} (x : _121532) (op : type1400 _121513) (f : _121532 -> _121513) (s : _121532 -> Prop) : (term137 _121513 _121532 op f x s) = (term138 _121513 _121532 x op f s).
Proof. exact (@lem5825654 _121532 _121513 x op f s). Qed.
Lemma lem5825656 {_121513 _121532 : Type'} (a : _121532) (op : type1400 _121513) (f : _121532 -> _121513) : (term71 _121513 _121532 op f a) = (term139 _121513 _121532 a op f).
Proof. exact (@lem5825655 _121513 _121532 a op f (@EMPTY _121532)). Qed.
Lemma lem5825662 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : (@support _119963 _120196 op f (@EMPTY _119963)) = (@EMPTY _119963).
Proof. exact (EQ_MP (@lem5825065 _119963 _120196 op f) (@lem5825064 _119963 _120196 op f)). Qed.
Lemma lem5825663 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) : (@support _121532 _121513 op f (@EMPTY _121532)) = (@EMPTY _121532).
Proof. exact (@lem5825662 _121532 _121513 op f). Qed.
Lemma lem5825664 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term140 _121513 _121532 f a op) = (term140 _121513 _121532 f a op).
Proof. exact (eq_refl (term140 _121513 _121532 f a op)). Qed.
Lemma lem5825665 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term141 _121513 _121532 a op f) = (term142 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825664 _121513 _121532 f a op) (@lem5825663 _121513 _121532 op f)). Qed.
Lemma lem5825667 {_119963 _120196 : Type'} (op : type1400 _120196) (f : _119963 -> _120196) : (@support _119963 _120196 op f (@EMPTY _119963)) = (@EMPTY _119963).
Proof. exact (EQ_MP (@lem5825065 _119963 _120196 op f) (@lem5825064 _119963 _120196 op f)). Qed.
Lemma lem5825668 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) : (@support _121532 _121513 op f (@EMPTY _121532)) = (@EMPTY _121532).
Proof. exact (@lem5825667 _121532 _121513 op f). Qed.
Lemma lem5825669 {_121532 : Type'} (a : _121532) : (@INSERT _121532 a) = (@INSERT _121532 a).
Proof. exact (eq_refl (@INSERT _121532 a)). Qed.
Lemma lem5825670 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term143 _121513 _121532 a op f) = (@INSERT _121532 a (@EMPTY _121532)).
Proof. exact (MK_COMB (@lem5825669 _121532 a) (@lem5825668 _121513 _121532 op f)). Qed.
Lemma lem5825671 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) : (term139 _121513 _121532 a op f) = (term144 _121513 _121532 f op a).
Proof. exact (MK_COMB (@lem5825665 _121513 _121532 f a op) (@lem5825670 _121513 _121532 op f a)). Qed.
Lemma lem5825674 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) : (term71 _121513 _121532 op f a) = (term144 _121513 _121532 f op a).
Proof. exact (TRANS (@lem5825656 _121513 _121532 a op f) (@lem5825671 _121513 _121532 f op a)). Qed.
Lemma lem5825675 {_121513 _121532 : Type'} (op : type1400 _121513) : (@iterate _121513 _121532 op) = (@iterate _121513 _121532 op).
Proof. exact (eq_refl (@iterate _121513 _121532 op)). Qed.
Lemma lem5825676 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) : (term123 _121513 _121532 op f a) = (term145 _121513 _121532 f op a).
Proof. exact (MK_COMB (@lem5825675 _121513 _121532 op) (@lem5825674 _121513 _121532 f op a)). Qed.
Lemma lem5825681 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term122 _121513 _121532 f a op) = (term122 _121513 _121532 f a op).
Proof. exact (eq_refl (term122 _121513 _121532 f a op)). Qed.
Lemma lem5825682 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term124 _121513 _121532 f a op) = (term146 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825676 _121513 _121532 f op a) (@lem5825681 _121513 _121532 f a op)). Qed.
Lemma lem5825683 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825684 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term126 _121513 _121532 f a op) = (term147 _121513 _121532 f a op).
Proof. exact (MK_COMB (@lem5825683 _121513) (@lem5825682 _121513 _121532 f a op)). Qed.
Lemma lem5825685 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem5825686 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : ((term124 _121513 _121532 f a op) = (f a)) = ((term146 _121513 _121532 f a op) = (f a)).
Proof. exact (MK_COMB (@lem5825684 _121513 _121532 f a op) (@lem5825685 _121513 _121532 f a)). Qed.
Lemma lem5825689 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : ((term146 _121513 _121532 f a op) = (f a)) = ((term124 _121513 _121532 f a op) = (f a)).
Proof. exact (SYM (@lem5825686 _121513 _121532 op f a)). Qed.
Lemma lem5825690 {_121532 : Type'} (_474 : _121532 -> Prop) (_475 : Prop) (_476 : type686 _121532) (_477 : _121532 -> Prop) : (term64 _121532 _476 _475 _474 _477) = (term65 _121532 _474 _475 _476 _477).
Proof. exact (@lem13473 (_121532 -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5825691 {_121513 _121532 : Type'} (_474 : _121532 -> Prop) (_475 : Prop) (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) (_477 : _121532 -> Prop) : (term148 _121513 _121532 op f a _475 _474 _477) = (term149 _121513 _121532 _474 _475 op f a _477).
Proof. exact (@lem5825690 _121532 _474 _475 (term150 _121513 _121532 op f a) _477). Qed.
Lemma lem5825692 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term151 _121513 _121532 f op a) = (term152 _121513 _121532 op f a).
Proof. exact (@lem5825691 _121513 _121532 (@EMPTY _121532) ((f a) = (@neutral _121513 op)) op f a (@INSERT _121532 a (@EMPTY _121532))). Qed.
Lemma lem5825693 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term153 _121513 _121532 op f a) = ((term154 _121513 _121532 f a op) = (f a)).
Proof. exact (eq_refl (term153 _121513 _121532 op f a)). Qed.
Lemma lem5825694 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term155 _121513 _121532 f a op) = (term155 _121513 _121532 f a op).
Proof. exact (eq_refl (term155 _121513 _121532 f a op)). Qed.
Lemma lem5825695 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term156 _121513 _121532 op f a) = (term157 _121513 _121532 op f a).
Proof. exact (MK_COMB (@lem5825694 _121513 _121532 f a op) (@lem5825693 _121513 _121532 op f a)). Qed.
Lemma lem5825696 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term158 _121513 _121532 op f a) = ((term159 _121513 _121532 f a op) = (f a)).
Proof. exact (eq_refl (term158 _121513 _121532 op f a)). Qed.
Lemma lem5825697 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term160 _121513 _121532 f a op) = (term160 _121513 _121532 f a op).
Proof. exact (eq_refl (term160 _121513 _121532 f a op)). Qed.
Lemma lem5825698 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term161 _121513 _121532 op f a) = (term162 _121513 _121532 op f a).
Proof. exact (MK_COMB (@lem5825697 _121513 _121532 f a op) (@lem5825696 _121513 _121532 op f a)). Qed.
Lemma lem5825699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5825700 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term163 _121513 _121532 op f a) = (term164 _121513 _121532 op f a).
Proof. exact (MK_COMB (@lem5825699) (@lem5825698 _121513 _121532 op f a)). Qed.
Lemma lem5825701 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term152 _121513 _121532 op f a) = (term165 _121513 _121532 op f a).
Proof. exact (MK_COMB (@lem5825700 _121513 _121532 op f a) (@lem5825695 _121513 _121532 op f a)). Qed.
Lemma lem5825702 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term151 _121513 _121532 f op a) = ((term146 _121513 _121532 f a op) = (f a)).
Proof. exact (eq_refl (term151 _121513 _121532 f op a)). Qed.
Lemma lem5825703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5825704 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term166 _121513 _121532 f op a) = (term167 _121513 _121532 op f a).
Proof. exact (MK_COMB (@lem5825703) (@lem5825702 _121513 _121532 op f a)). Qed.
Lemma lem5825705 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : ((term151 _121513 _121532 f op a) = (term152 _121513 _121532 op f a)) = (((term146 _121513 _121532 f a op) = (f a)) = (term165 _121513 _121532 op f a)).
Proof. exact (MK_COMB (@lem5825704 _121513 _121532 op f a) (@lem5825701 _121513 _121532 op f a)). Qed.
Lemma lem5825706 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : ((term146 _121513 _121532 f a op) = (f a)) = (term165 _121513 _121532 op f a).
Proof. exact (EQ_MP (@lem5825705 _121513 _121532 op f a) (@lem5825692 _121513 _121532 op f a)). Qed.
Lemma lem5825707 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term165 _121513 _121532 op f a) = ((term146 _121513 _121532 f a op) = (f a)).
Proof. exact (SYM (@lem5825706 _121513 _121532 op f a)). Qed.
Lemma lem5825708 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : (f a) = (@neutral _121513 op)) : (f a) = (@neutral _121513 op).
Proof. exact (h1). Qed.
Lemma lem5825758 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term127 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5825759 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term127 _120477 _120519 _120521 op) = (term128 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term127 _120477 _120519 _120521 op)). Qed.
Lemma lem5825760 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term128 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5825759 _120477 _120519 _120521 op) (@lem5825758 _120477 _120519 _120521 op)). Qed.
Lemma lem5825761 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5825762 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term129 _120477 _120519 _120521 op.
Proof. exact (@lem5825760 _120477 _120519 _120521 op (@lem5825761 _120519 op h1)). Qed.
Lemma lem5825785 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term130 _120477 _120519 op.
Proof. exact (proj1 (@lem5825762 _120477 _120519 Prop op h1)). Qed.
Lemma lem5825786 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term131 _120477 _120519 op f.
Proof. exact (@lem5825785 _120477 _120519 op h1 f). Qed.
Lemma lem5825787 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term131 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term131 _120477 _120519 op f)). Qed.
Lemma lem5825788 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5825787 _120477 _120519 f op) (@lem5825786 _120477 _120519 f op h1)). Qed.
Lemma lem5825794 {_121513 : Type'} (op : type1400 _121513) : (@monoidal _121513 op) = ((@monoidal _121513 op) = True).
Proof. exact (@lem7 (@monoidal _121513 op)). Qed.
Lemma lem5825801 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term132 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5825788 _120477 _120519 f op h0). Qed.
Lemma lem5825802 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) : term133 _121513 _121532 f op.
Proof. exact (@lem5825801 _121532 _121513 f op). Qed.
Lemma lem5825803 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : term168 _121513 _121532 f a op.
Proof. exact (@lem5825802 _121513 _121532 (term122 _121513 _121532 f a op) op). Qed.
Lemma lem5825805 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : (@monoidal _121513 op) = True.
Proof. exact (EQ_MP (@lem5825794 _121513 op) (@lem5825106 _121513 op h1)). Qed.
Lemma lem5825806 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : True = (@monoidal _121513 op).
Proof. exact (SYM (@lem5825805 _121513 op h1)). Qed.
Lemma lem5825807 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : @monoidal _121513 op.
Proof. exact (EQ_MP (@lem5825806 _121513 op h1) (@lem0)). Qed.
Lemma lem5825808 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term159 _121513 _121532 f a op) = (@neutral _121513 op).
Proof. exact (@lem5825803 _121513 _121532 f a op (@lem5825807 _121513 op h1)). Qed.
Lemma lem5825809 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825810 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term169 _121513 _121532 f a op) = (term136 _121513 op).
Proof. exact (MK_COMB (@lem5825809 _121513) (@lem5825808 _121513 _121532 f a op h1)). Qed.
Lemma lem5825812 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : (f a) = (@neutral _121513 op)) : (f a) = (@neutral _121513 op).
Proof. exact (h1). Qed.
Lemma lem5825813 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) (h2 : (f a) = (@neutral _121513 op)) : ((term159 _121513 _121532 f a op) = (f a)) = ((@neutral _121513 op) = (@neutral _121513 op)).
Proof. exact (MK_COMB (@lem5825810 _121513 _121532 f a op h1) (@lem5825812 _121513 _121532 f a op h2)). Qed.
Lemma lem5825815 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5825816 {_121513 : Type'} (x : _121513) : (x = x) = True.
Proof. exact (@lem5825815 _121513 x). Qed.
Lemma lem5825817 {_121513 : Type'} (op : type1400 _121513) : ((@neutral _121513 op) = (@neutral _121513 op)) = True.
Proof. exact (@lem5825816 _121513 (@neutral _121513 op)). Qed.
Lemma lem5825818 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) (h2 : (f a) = (@neutral _121513 op)) : ((term159 _121513 _121532 f a op) = (f a)) = True.
Proof. exact (TRANS (@lem5825813 _121513 _121532 f a op h1 h2) (@lem5825817 _121513 op)). Qed.
Lemma lem5825819 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) (h2 : (f a) = (@neutral _121513 op)) : True = ((term159 _121513 _121532 f a op) = (f a)).
Proof. exact (SYM (@lem5825818 _121513 _121532 f a op h1 h2)). Qed.
Lemma lem5825821 {A B : Type'} (op : type1400 B) : term170 A B op.
Proof. exact (@lem5807175 A B op). Qed.
Lemma lem5825822 {A B : Type'} (op : type1400 B) : (term170 A B op) = (term171 A B op).
Proof. exact (eq_refl (term170 A B op)). Qed.
Lemma lem5825823 {A B : Type'} (op : type1400 B) : term171 A B op.
Proof. exact (EQ_MP (@lem5825822 A B op) (@lem5825821 A B op)). Qed.
Lemma lem5825824 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5825825 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term172 A B op.
Proof. exact (@lem5825823 A B op (@lem5825824 B op h1)). Qed.
Lemma lem5825826 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term173 A B op f.
Proof. exact (@lem5825825 A B op h1 f). Qed.
Lemma lem5825827 {A B : Type'} (op : type1400 B) (f : A -> B) : (term173 A B op f) = (term174 A B op f).
Proof. exact (eq_refl (term173 A B op f)). Qed.
Lemma lem5825828 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term174 A B op f.
Proof. exact (EQ_MP (@lem5825827 A B op f) (@lem5825826 A B f op h1)). Qed.
Lemma lem5825829 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term175 A B op f x.
Proof. exact (@lem5825828 A B f op h1 x). Qed.
Lemma lem5825830 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term175 A B op f x) = ((term176 A B op x f) = (f x)).
Proof. exact (eq_refl (term175 A B op f x)). Qed.
Lemma lem5825831 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term176 A B op x f) = (f x).
Proof. exact (EQ_MP (@lem5825830 A B op f x) (@lem5825829 A B f x op h1)). Qed.
Lemma lem5825873 {_121513 : Type'} (op : type1400 _121513) : (@monoidal _121513 op) = ((@monoidal _121513 op) = True).
Proof. exact (@lem7 (@monoidal _121513 op)). Qed.
Lemma lem5825893 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term177 A B op f x.
Proof. exact (fun h0 : @monoidal B op => @lem5825831 A B f x op h0). Qed.
Lemma lem5825894 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (x : _121532) : term178 _121513 _121532 op f x.
Proof. exact (@lem5825893 _121532 _121513 op f x). Qed.
Lemma lem5825895 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) : term179 _121513 _121532 f op a.
Proof. exact (@lem5825894 _121513 _121532 op (term122 _121513 _121532 f a op) a). Qed.
Lemma lem5825897 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : (@monoidal _121513 op) = True.
Proof. exact (EQ_MP (@lem5825873 _121513 op) (@lem5825106 _121513 op h1)). Qed.
Lemma lem5825898 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : True = (@monoidal _121513 op).
Proof. exact (SYM (@lem5825897 _121513 op h1)). Qed.
Lemma lem5825899 {_121513 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : @monoidal _121513 op.
Proof. exact (EQ_MP (@lem5825898 _121513 op h1) (@lem0)). Qed.
Lemma lem5825900 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term154 _121513 _121532 f a op) = (term180 _121513 _121532 f op a).
Proof. exact (@lem5825895 _121513 _121532 f op a (@lem5825899 _121513 op h1)). Qed.
Lemma lem5825902 {A B : Type'} (f : A -> B) (y : A) : (term181 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5825903 {_121513 _121532 : Type'} (f : _121532 -> _121513) (y : _121532) : (term182 _121513 _121532 f y) = (f y).
Proof. exact (@lem5825902 _121532 _121513 f y). Qed.
Lemma lem5825904 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) : (term183 _121513 _121532 f op a) = (term180 _121513 _121532 f op a).
Proof. exact (@lem5825903 _121513 _121532 (term122 _121513 _121532 f a op) a). Qed.
Lemma lem5825905 {_121513 _121532 : Type'} (x : _121532) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term184 _121513 _121532 f a op x) = (term121 _121513 _121532 x f a op).
Proof. exact (eq_refl (term184 _121513 _121532 f a op x)). Qed.
Lemma lem5825906 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term185 _121513 _121532 f a op) = (term122 _121513 _121532 f a op).
Proof. exact (fun_ext (fun x : _121532 => @lem5825905 _121513 _121532 x f a op)). Qed.
Lemma lem5825907 {_121532 : Type'} (a : _121532) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5825908 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) : (term183 _121513 _121532 f op a) = (term180 _121513 _121532 f op a).
Proof. exact (MK_COMB (@lem5825906 _121513 _121532 f a op) (@lem5825907 _121532 a)). Qed.
Lemma lem5825909 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825910 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) : (term186 _121513 _121532 f op a) = (term187 _121513 _121532 f op a).
Proof. exact (MK_COMB (@lem5825909 _121513) (@lem5825908 _121513 _121532 f op a)). Qed.
Lemma lem5825911 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term180 _121513 _121532 f op a) = (term188 _121513 _121532 f a op).
Proof. exact (eq_refl (term180 _121513 _121532 f op a)). Qed.
Lemma lem5825912 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : ((term183 _121513 _121532 f op a) = (term180 _121513 _121532 f op a)) = ((term180 _121513 _121532 f op a) = (term188 _121513 _121532 f a op)).
Proof. exact (MK_COMB (@lem5825910 _121513 _121532 f op a) (@lem5825911 _121513 _121532 f a op)). Qed.
Lemma lem5825913 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) : (term180 _121513 _121532 f op a) = (term188 _121513 _121532 f a op).
Proof. exact (EQ_MP (@lem5825912 _121513 _121532 f a op) (@lem5825904 _121513 _121532 f op a)). Qed.
Lemma lem5825915 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term189 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem5825916 {_121513 _121532 : Type'} (x : _121532) (z : _121513) (y : _121513) : (term189 _121513 _121532 x y z) = y.
Proof. exact (@lem5825915 _121513 _121532 x z y). Qed.
Lemma lem5825917 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term188 _121513 _121532 f a op) = (f a).
Proof. exact (@lem5825916 _121513 _121532 a (@neutral _121513 op) (f a)). Qed.
Lemma lem5825918 {_121513 _121532 : Type'} (op : type1400 _121513) (f : _121532 -> _121513) (a : _121532) : (term180 _121513 _121532 f op a) = (f a).
Proof. exact (TRANS (@lem5825913 _121513 _121532 f a op) (@lem5825917 _121513 _121532 op f a)). Qed.
Lemma lem5825919 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term154 _121513 _121532 f a op) = (f a).
Proof. exact (TRANS (@lem5825900 _121513 _121532 f a op h1) (@lem5825918 _121513 _121532 op f a)). Qed.
Lemma lem5825920 {_121513 : Type'} : (@eq _121513) = (@eq _121513).
Proof. exact (eq_refl (@eq _121513)). Qed.
Lemma lem5825921 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term190 _121513 _121532 f a op) = (term191 _121513 _121532 f a).
Proof. exact (MK_COMB (@lem5825920 _121513) (@lem5825919 _121513 _121532 f a op h1)). Qed.
Lemma lem5825922 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem5825923 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : ((term154 _121513 _121532 f a op) = (f a)) = ((f a) = (f a)).
Proof. exact (MK_COMB (@lem5825921 _121513 _121532 f a op h1) (@lem5825922 _121513 _121532 f a)). Qed.
Lemma lem5825925 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5825926 {_121513 : Type'} (x : _121513) : (x = x) = True.
Proof. exact (@lem5825925 _121513 x). Qed.
Lemma lem5825927 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) : ((f a) = (f a)) = True.
Proof. exact (@lem5825926 _121513 (f a)). Qed.
Lemma lem5825928 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : ((term154 _121513 _121532 f a op) = (f a)) = True.
Proof. exact (TRANS (@lem5825923 _121513 _121532 f a op h1) (@lem5825927 _121513 _121532 f a)). Qed.
Lemma lem5825929 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : True = ((term154 _121513 _121532 f a op) = (f a)).
Proof. exact (SYM (@lem5825928 _121513 _121532 f a op h1)). Qed.
Lemma lem5825931 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term154 _121513 _121532 f a op) = (f a).
Proof. exact (EQ_MP (@lem5825929 _121513 _121532 f a op h1) (@lem0)). Qed.
Lemma lem5825932 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term157 _121513 _121532 op f a.
Proof. exact (fun h0 : term192 _121513 _121532 f a op => @lem5825931 _121513 _121532 f a op h1). Qed.
Lemma lem5825933 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) (h2 : (f a) = (@neutral _121513 op)) : (term159 _121513 _121532 f a op) = (f a).
Proof. exact (EQ_MP (@lem5825819 _121513 _121532 f a op h1 h2) (@lem0)). Qed.
Lemma lem5825934 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) (h2 : (f a) = (@neutral _121513 op)) : ((f a) = (@neutral _121513 op)) = ((term159 _121513 _121532 f a op) = (f a)).
Proof. exact (prop_ext (fun h3 : (f a) = (@neutral _121513 op) => @lem5825933 _121513 _121532 f a op h1 h2) (fun h3 : (term159 _121513 _121532 f a op) = (f a) => @lem5825708 _121513 _121532 f a op h2)). Qed.
Lemma lem5825935 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) (h2 : (f a) = (@neutral _121513 op)) : (term159 _121513 _121532 f a op) = (f a).
Proof. exact (EQ_MP (@lem5825934 _121513 _121532 f a op h1 h2) (@lem5825708 _121513 _121532 f a op h2)). Qed.
Lemma lem5825936 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term162 _121513 _121532 op f a.
Proof. exact (fun h0 : (f a) = (@neutral _121513 op) => @lem5825935 _121513 _121532 f a op h1 h0). Qed.
Lemma lem5825937 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term165 _121513 _121532 op f a.
Proof. exact (conj (@lem5825936 _121513 _121532 f a op h1) (@lem5825932 _121513 _121532 f a op h1)). Qed.
Lemma lem5825938 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term146 _121513 _121532 f a op) = (f a).
Proof. exact (EQ_MP (@lem5825707 _121513 _121532 op f a) (@lem5825937 _121513 _121532 f a op h1)). Qed.
Lemma lem5825939 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term124 _121513 _121532 f a op) = (f a).
Proof. exact (EQ_MP (@lem5825689 _121513 _121532 op f a) (@lem5825938 _121513 _121532 f a op h1)). Qed.
Lemma lem5825940 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term78 _121513 _121532 a f op) = (term90 _121513 _121532 f a op).
Proof. exact (EQ_MP (@lem5825585 _121513 _121532 f a op) (@lem5825939 _121513 _121532 f a op h1)). Qed.
Lemma lem5825941 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @monoidal _121513 op) (h2 : term93 _121532 a s) : (term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem5825241 _121513 _121532 f op a s h2) (@lem5825650 _121513 _121532 f a op h1)). Qed.
Lemma lem5825942 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @monoidal _121513 op) (h2 : term93 _121532 a s) : (term93 _121532 a s) = ((term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (prop_ext (fun h3 : term93 _121532 a s => @lem5825941 _121513 _121532 f op a s h1 h2) (fun h3 : (term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op) => @lem5825226 _121532 a s h2)). Qed.
Lemma lem5825943 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @monoidal _121513 op) (h2 : term93 _121532 a s) : (term73 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem5825942 _121513 _121532 f op a s h1 h2) (@lem5825226 _121532 a s h2)). Qed.
Lemma lem5825944 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term76 _121513 _121532 s f a op.
Proof. exact (fun h0 : term93 _121532 a s => @lem5825943 _121513 _121532 f op a s h1 h0). Qed.
Lemma lem5825945 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @monoidal _121513 op) (h2 : @IN _121532 a s) : (term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem5825225 _121513 _121532 f op a s h2) (@lem5825940 _121513 _121532 f a op h1)). Qed.
Lemma lem5825946 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @monoidal _121513 op) (h2 : @IN _121532 a s) : (@IN _121532 a s) = ((term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op)).
Proof. exact (prop_ext (fun h3 : @IN _121532 a s => @lem5825945 _121513 _121532 f op a s h1 h2) (fun h3 : (term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op) => @lem5825210 _121532 a s h2)). Qed.
Lemma lem5825947 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (a : _121532) (s : _121532 -> Prop) (h1 : @monoidal _121513 op) (h2 : @IN _121532 a s) : (term78 _121513 _121532 a f op) = (term41 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem5825946 _121513 _121532 f op a s h1 h2) (@lem5825210 _121532 a s h2)). Qed.
Lemma lem5825948 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term81 _121513 _121532 s f a op.
Proof. exact (fun h0 : @IN _121532 a s => @lem5825947 _121513 _121532 f op a s h1 h0). Qed.
Lemma lem5825949 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term84 _121513 _121532 s f a op.
Proof. exact (conj (@lem5825948 _121513 _121532 s f a op h1) (@lem5825944 _121513 _121532 s f a op h1)). Qed.
Lemma lem5825950 {_121513 _121532 : Type'} (s : _121532 -> Prop) (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : (term56 _121513 _121532 s a f op) = (term41 _121513 _121532 s f a op).
Proof. exact (EQ_MP (@lem5825209 _121513 _121532 s f a op) (@lem5825949 _121513 _121532 s f a op h1)). Qed.
Lemma lem5825955 {_121513 _121532 : Type'} (f : _121532 -> _121513) (a : _121532) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term59 _121513 _121532 f a op.
Proof. exact (fun s : _121532 -> Prop => @lem5825950 _121513 _121532 s f a op h1). Qed.
Lemma lem5825960 {_121513 _121532 : Type'} (f : _121532 -> _121513) (op : type1400 _121513) (h1 : @monoidal _121513 op) : term61 _121513 _121532 f op.
Proof. exact (fun a : _121532 => @lem5825955 _121513 _121532 f a op h1). Qed.
Lemma lem5825965 {_121513 _121532 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : term63 _121513 _121532 op.
Proof. exact (fun f : _121532 -> _121513 => @lem5825960 _121513 _121532 f op h1). Qed.
Lemma lem5825966 {_121513 _121532 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : term53 _121513 _121532 op.
Proof. exact (EQ_MP (@lem5825191 _121513 _121532 op) (@lem5825965 _121513 _121532 op h1)). Qed.
Lemma lem5825967 {_121513 _121532 : Type'} (op : type1400 _121513) (h1 : @monoidal _121513 op) : term52 _121513 _121532 op.
Proof. exact (EQ_MP (@lem5825138 _121513 _121532 op) (@lem5825966 _121513 _121532 op h1)). Qed.
Lemma lem5825968 {_121513 _121532 : Type'} (op : type1400 _121513) : term193 _121513 _121532 op.
Proof. exact (fun h0 : @monoidal _121513 op => @lem5825967 _121513 _121532 op h0). Qed.
Lemma lem5825973 {_121513 _121532 : Type'} : term194 _121513 _121532.
Proof. exact (fun op : type1400 _121513 => @lem5825968 _121513 _121532 op). Qed.
