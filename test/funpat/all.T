eval pass fpat001.curry goal
eval fail fpat002.curry goal1 X where X free
eval fail fpat002.curry goal2 X where X free
eval pass fpat003.curry goal1 X where X free
eval fail fpat003.curry goal2 X where X free
eval fail fpat003.curry goal3 X where X free
eval pass fpat004.curry main
eval pass fpat005.curry main
eval pass fpat006.curry main
eval pass fpat007.curry main
eval pass fpat008.curry main
eval pass fpat009.curry coin inst_Num_Int x where x free
eval pass fpat009.curry coin inst_Num_Float x where x free
eval pass fpat010.curry main
eval pass fpat011.curry goal t where t free
eval pass fpat012.curry main
eval pass fpat013.curry main
eval pass fpat014.curry main
eval fail fpat015.curry goal1 x where x free
eval fail fpat015.curry goal2 x where x free
eval fail fpat015.curry goal3
skip_eval pass fpat016.curry goal1
eval pass fpat016.curry goal2
eval pass fpat017.curry goal1
eval fail fpat017.curry goal2
eval fail fpat017.curry goal3
eval pass fpat017.curry goal4
eval fail fpat017.curry goal5
eval pass fpat017.curry goal6
eval fail fpat017.curry goal7
eval pass fpat017.curry goal8
eval fail fpat017.curry goal9
type pass fpat018.curry g
type pass fpat018.curry g'
type pass fpat018.curry h
type pass fpat018.curry h'
compile fail fpat019.curry
compile fail fpat020.curry
type pass fpat021.curry f
type pass fpat021.curry g
