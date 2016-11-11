#Remove lines from file that were commented out

def clean(inputpath,outputpath):
	with open(inputpath) as inf, open(outputpath,"w") as of:
		for line in inf:
			stripped = line.lstrip()
			skip = stripped.startswith("//") #or line.strip() == ""
			if not skip:
				of.write(line)
