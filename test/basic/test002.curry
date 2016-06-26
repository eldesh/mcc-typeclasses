-- The runtime system implements an optimization to avoid stacking update
-- frames by linking the queue-me node from an update frame to the
-- queue-me node of the current application. However, this optimization
-- must not be applied when both nodes are equal. Here are some simple
-- examples where this is the case.

goal1 = let x = id x in x
goal2 = let x = const (id x) _ in x
goal3 = let x = id y; y = id x in x
