theory model
imports HHL
begin

definition T :: exp where
"T == Real 0.01"
definition t :: exp where
"t == RVar ''t''"
definition h :: exp where
"h == RVar ''h''"
definition v :: exp where
"v == RVar ''v''"
consts Qmax :: exp
consts pi :: exp
consts g :: exp
consts r :: exp

consts c2p :: cname
consts p2c :: cname

definition x :: exp where
"x == RVar ''x''"
definition y :: exp where
"y == RVar ''y''"

definition conProp :: fform where
"conProp == (y[=](Real 0) [|] y[=](Real 1))"

definition inv :: fform where
"inv == t[>=](Real 0) [&] t[<=]T [&] (v[=](Real 1) [&] (h[>=](Real 0.30) [&] h[*](Real 1000)[<=](Real 590)[+](Real 3)[*]t) [|] (v[=](Real 0) [&] h[<=](Real 0.60) [&] h[*](Real 1000)[>=](Real 310) [-] (Real 7)[*]t))"
definition invT0 :: fform where
"invT0 == (v[=](Real 1) [&] (h[>=](Real 0.30) [&] h[<=](Real 0.59)) [|] (v[=](Real 0) [&] h[<=](Real 0.60) [&] h[>=](Real 0.31)))"
definition invX :: fform where
"invX == x[=]h [&] t[>=](Real 0) [&] t[<=]T [&] (v[=](Real 1) [&] (x[>=](Real 0.30) [&] x[*](Real 1000)[<=](Real 590)[+](Real 3)[*]t) [|] (v[=](Real 0) [&] x[<=](Real 0.60) [&] x[*](Real 1000)[>=](Real 310) [-] (Real 7)[*]t)) [&] conProp"
definition invXY :: fform where
"invXY == x[=]h [&] t[>=](Real 0) [&] t[<=]T [&] (v[=](Real 1) [&] (x[>=](Real 0.30) [&] x[*](Real 1000)[<=](Real 590)[+](Real 3)[*]t) [|] (v[=](Real 0) [&] x[<=](Real 0.60) [&] x[*](Real 1000)[>=](Real 310) [-] (Real 7)[*]t)) [&] ((y[=](Real 1) [|] x[>](Real 0.31))) [&] conProp"
definition invXY0 :: fform where
"invXY0 == x[=]h [&] t[>=](Real 0) [&] t[<=]T [&] (y[=](Real 1) [&] (x[>=](Real 0.30) [&] x[<=](Real 0.59)) [|] (y[=](Real 0) [&] x[<=](Real 0.60) [&] x[>=](Real 0.31))) [&] conProp"

definition init :: fform where
"init == (t[=](Real 0)) [&] (h[=](Real 0.31)) [&] (v[=](Real 1))"
definition post :: fform where
"post == (h[>=](Real 0.30)) [&] (h[<=](Real 0.60))"
definition H :: fform where
"H == high (post)"

definition mid0 :: "mid" where
"mid0 == (inv, (high inv) [&] (l[=]T))"
definition mid1 :: "mid" where
"mid1 == (invT0, (high inv) [&] (l[=]T))"
definition mid2 :: "mid" where
"mid2 == (conProp, (l[=]T))"
definition mid3 :: "mid" where
"mid3 == (invX, (l[=]T))"
definition mid4 :: "mid" where
"mid4 == (invXY, (l[=](Real 0)))"
definition mid5 :: "mid" where
"mid5 == (invXY0, (l[=]T))"


definition Plant :: proc where
"Plant ==  (((<inv && (t[<]T)> : (l[=]T)) [[> (p2c !! h)); mid0; (c2p ?? v)); mid1; (t:=(Real 0))"

definition Control :: proc where
"Control ==(((<conProp && WTrue> : (l[=]T)); mid2; p2c??x); mid3; ((IF (x[<=](Real 0.31)) (y:=(Real 1))); mid4; (IF (x[>=](Real 0.59)) (y:=(Real 0))))); mid5; c2p!!y"

definition WLCS :: proc where
"WLCS == (Plant *) || (Control *)"

lemma "{init, conProp} WLCS {post, conProp; H, WTrue}"
apply (simp add: WLCS_def)
apply (cut_tac px= "inv" and py="conProp" and qx="inv" and qy="conProp" and Hx="high inv " and Hy="WTrue" in ConsequenceP,auto)
prefer 2
(*to inv*)
apply (rule conjR)
apply (rule Trans)
apply (simp add: init_def inv_def v_def h_def t_def equal_greater_def equal_less_def T_def)
apply (rule conjR)
apply (rule Trans)
apply (simp add: init_def inv_def v_def h_def t_def equal_greater_def equal_less_def)
apply (rule conjR)
apply (simp add: inv_def post_def)
apply (rule impR)
apply (rule conjL, rule conjL)
apply (rule disjL)
apply (rule conjR)
apply (rule Trans3)
apply (simp add: init_def inv_def v_def h_def t_def equal_greater_def equal_less_def post_def T_def)
apply (rule conjL)+
apply (cut_tac P="v [=] Real 1" in thinL, auto)
apply (cut_tac P="h [>=] Real 3 / 10" in thinL, auto)
apply (rule Trans3)
apply (simp add: init_def inv_def v_def h_def t_def equal_greater_def equal_less_def post_def T_def)
apply smt
apply (rule Trans3)
apply (simp add: init_def inv_def v_def h_def t_def equal_greater_def equal_less_def post_def T_def)
apply smt
apply (rule conjR, rule impR, rule basic)
apply (rule conjR, rule impR)
apply (simp add: H_def)
apply (rule DC18)
apply (simp add: inv_def post_def)
apply (rule conjL, rule conjL)
apply (rule disjL)
apply (rule Trans3)
apply (simp add: init_def inv_def v_def h_def t_def equal_greater_def equal_less_def post_def T_def)
apply smt
apply (rule Trans3)
apply (simp add: init_def inv_def v_def h_def t_def equal_greater_def equal_less_def post_def T_def)
apply smt
apply (rule impR, rule basic)
(*rep*)
apply (rule Repetition)
defer
(*to inv*)
apply (rule impR)
apply (rule DCR3, rule basic)
apply (rule impR, rule thinL, rule Trans, simp)
(*one*)
apply (cut_tac px= "inv" and py="conProp" and qx="inv" and qy="conProp" and Hx="(high inv) [&] (l[=]T)" and Hy="WTrue [&] (l[=]T)" in ConsequenceP,auto)
prefer 2
apply (rule Trans, simp)
apply (simp add: Plant_def Control_def)
apply (rule Structure)
apply (simp add: mid5_def mid1_def)
apply (cut_tac Gy="l[=](Real 0)" in Parallel1a, auto)
defer
apply (rule Assign, auto)
apply (simp add: inv_def equal_greater_def equal_less_def)
apply (rule Trans)
apply (simp add: invT0_def t_def inv_def init_def inv_def v_def h_def t_def equal_greater_def equal_less_def T_def)
apply smt
apply (rule impR, rule LL4, rule basic)
(*comm1*)
apply (simp add: mid0_def)
apply (rule Communication1, auto)
apply (simp add: invT0_def equal_greater_def equal_less_def)
defer
apply (rule conjR, rule impR)
apply (simp add: invXY0_def)
apply (rule conjL)+
apply (rule basic)
apply (rule impR, rule conjL, cut_tac P="inv" in thinL, auto)
apply (simp add: invXY0_def invT0_def v_def y_def h_def equal_greater_def equal_less_def x_def)
apply (rule conjL)+
apply (cut_tac P="t [>] Real 0 [|] t [=] Real 0" in thinL, auto)
apply (cut_tac P="t [<] T [|] t [=] T" in thinL, auto)
apply (cut_tac P="conProp" in thinL, auto)
apply (rule Trans2, simp)
apply (metis zero_neq_one)
apply (rule conjR, rule impR, rule thinL, rule Trans, simp)
apply (rule impR, rule LC1)
apply (rule DCL3)
apply (rule basic)
apply (rule Trans, simp)
(*ass*)
apply (rule Structure)
apply (simp add: mid3_def)
apply (cut_tac Gy="l[=](Real 0)" in Parallel1a, auto)
defer
apply (cut_tac px="invX" and qx="invXY0" and Hx="(l[=](Real 0))[^](l[=](Real 0))" in ConsequenceS, auto)
apply (simp add: mid4_def)
apply (rule Sequence)
apply (cut_tac b="(x [<=] Real 31 / 100)" in Case, auto)
apply (rule ConditionT)
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: invXY_def conProp_def equal_greater_def equal_less_def)
apply (rule conjR)
apply (simp add: x_def y_def invX_def invXY_def equal_greater_def equal_less_def t_def T_def h_def v_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule thinL)+
apply (rule Trans, simp add: conProp_def y_def)
apply (rule impR, rule basic)
apply (rule ConditionF)
apply (rule Trans, simp)
apply (simp add: x_def y_def invX_def invXY_def equal_greater_def equal_less_def t_def T_def h_def v_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule conjR, rule thinL)
apply (rule disjR, rule thinR)
apply (rule Trans1, simp)
apply (rule basic)
apply (rule impR, rule basic)
apply (cut_tac b="(x [>=] Real 59 / 100)" in Case, auto)
apply (rule ConditionT)
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: invXY0_def conProp_def equal_greater_def equal_less_def)
apply (rule conjR)
apply (simp add: invXY_def invXY0_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def conProp_def)
apply (rule Trans, simp)
apply smt
apply (rule impR, rule basic)
apply (rule ConditionF)
apply (rule Trans, simp)
apply (simp add: invXY_def invXY0_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (cut_tac P="x [>=] Real 3 / 10" in cut, auto)
apply (rule thinR)
apply (rule thinL, rule thinL)
apply (cut_tac P="conProp" in thinL, auto)
apply (rule Trans4)
apply (simp add: invXY_def invXY0_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def)
apply smt
apply (rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans4, simp add: conProp_def x_def y_def equal_greater_def equal_less_def)
apply metis
apply (rule basic)
apply (rule impR, rule basic)
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)+
(*comm2*)
apply (simp add: mid2_def)
apply (cut_tac Hy="l[=]T" and H="l[=]T" and pre="inv" and Init="WTrue" in CommunicationI1b, auto) 
apply (simp add: invX_def conProp_def equal_greater_def equal_less_def)
apply (rule impR, rule basic)
apply (rule impR, rule RL3)
apply (cut_tac R=WTrue in CMR, auto)
apply (rule basic)
apply (rule thinL, rule Trans, simp)
apply (cut_tac px="conProp [&] WTrue" and qx="conProp" and Hx="l [=] T" in ConsequenceS, auto)
apply (rule Continue)
prefer 6
apply (simp add: invXY_def invXY0_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def)
apply (simp add: invX_def inv_def equal_greater_def equal_less_def t_def T_def h_def v_def y_def x_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, simp)
apply (rule conjR, rule basic)+
apply (simp add: conProp_def y_def, rule basic)
prefer 6
apply (rule impR)
apply (rule conjL)+
apply (rule disjL)
apply (rule Trans2, simp add: ltrans T_def)
apply (metis mult_zero_left zero_neq_one)
apply (rule conjR)
apply (cut_tac P="l[=]T" in thinL, auto)
apply (rule DC18)
apply (rule conjL)+
apply (rule basic)+
apply (rule Trans, simp add: conProp_def)+
done

end
