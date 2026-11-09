# FROZEN -- documents closed at the rollover cap, with the line count they were closed at.
#
# A frozen document keeps its NAME and its LINE COUNT exactly as they are, because
# citations across the project resolve into it by line.  Nothing is ever appended to it,
# nothing is ever deleted from it, and it is never renamed.  Its successor names it in its
# own first lines.  rollover.py reads this register: a document named here is not counted
# as live, and if its line count has moved since it was frozen that is a row.
#
# The cap and the reason for it are in discipline/rollover.py.
#
# | document | lines when frozen | bytes when frozen | successor |
# |---|---|---|---|
