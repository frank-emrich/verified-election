#Tries to delete conjuncts from invaraints (lines starting with &&) and assertions (lines starting with assert) and then compile the BASE_FILE_PATH
#WORKER_THREADS is somehow also the number of processes, because each worker thread spawns a dafny process

import math, shutil, subprocess, sys, time
import concurrent.futures, threading, os, queue
import psutil

BASE_FILE_PATH = "election.dfy"
WORKD_DIR="workdir"
GOOD_DIR="works"
TIMEOUT_SECONDS=200
WORKER_THREADS=6
OUTPUT_FILE="output/working"
STATISTICS_INTERVAL_SECONDS=60
QUEUE_POLL_INTERVALL_SECONDS=1

seenLock = threading.Lock()
goodConfigLock = threading.Lock()
printLock = threading.Lock()
futureLock = threading.Lock()


pool = concurrent.futures.ThreadPoolExecutor(max_workers=(1+WORKER_THREADS)) #One pool slot is for statistics printer
seenconfig = set([])
goodconfigs = set([])
futures = []
outputFileCounter = 0

q = queue.Queue()

def safePrint(message):
    with printLock:
        print(message)

def determineDeletionCandidates(file):
    lineIndex = 1
    candiates = []
    for line in file:
        line = line.lstrip()
        #print(line)
        canDelete = line.startswith("assert") or line.startswith("&&")
        if canDelete:
            candiates.append(lineIndex)
        lineIndex += 1
    return frozenset(candiates)


def createModifiedCopy(linesToDelete):
    newPath = hashOfConfig(linesToDelete)
    #print(newPath)
    baseFile = open(BASE_FILE_PATH)
    newFileRelPath = WORKD_DIR + "/set" + newPath + ".dfy"
    targetFile = open(newFileRelPath , 'w+')
    newFileAbsPath = os.path.abspath(newFileRelPath)
    
    lineIndex = 1
    for line in baseFile:
        if lineIndex in linesToDelete and not line.startswith("//"):
            targetFile.write("// diet! " + line)
        else:
            targetFile.write(line)
        lineIndex += 1

    return newFileAbsPath


def runDafny(absolutePath):
    return timeout_command(["dafny",absolutePath],TIMEOUT_SECONDS)

def timeout_command(command, timeout):
    """call shell-command and either return its output or kill it
    if it doesn't normally exit within timeout seconds and return None"""
    import subprocess, datetime, os, time, signal
    start = datetime.datetime.now()
    process = subprocess.Popen(command, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    safePrint("Started " +  str(process.pid))
    while process.poll() is None:
      time.sleep(5)
      now = datetime.datetime.now()
      if (now - start).seconds> timeout:
        #subprocess.Popen(["taskkill", "/f", "/t", "/pid " + str(process.pid)], shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        killProcessAndChildren(process.pid)
        #os.kill(process.pid, signal.SIGKILL)
        #os.waitpid(-1, os.WNOHANG)
        safePrint("Killed " +  str(process.pid))
        return False
    return True if process.returncode == 0 else False

def killProcessAndChildren(pid):
    parent = psutil.Process(pid)
    children = parent.children(recursive=True)  # or parent.children() for recursive=False
    for child in children:
        child.kill()
    parent.kill()

def hashOfConfig(deletionSet):
    return str(int(math.fabs(hash(deletionSet))))

def logWorkingConfig(workingConfig):
    hashStr = hashOfConfig(workingConfig)
    workingPath =  WORKD_DIR + "/set" + hashStr + ".dfy"
    goodStorePath = GOOD_DIR + "/" + str(len(workingConfig)) + "_" + hashStr + ".dfy"
    shutil.copyfile(workingPath, goodStorePath)
    safePrint("Works: " + str(workingConfig)+ "/" + hashOfConfig(workingConfig))
    with goodConfigLock:
        goodconfigs.add(workingConfig)

def execute(linesToDelete, remainingLines):
    safePrint("Working on: "+ str(linesToDelete) + "/" + hashOfConfig(linesToDelete))
    seenLock.acquire()

    seenconfig.add(linesToDelete)
    seenLock.release()

    path = createModifiedCopy(linesToDelete)

    versionCompiles = runDafny(path)
    safePrint("Dafny for " + str(linesToDelete)+ "/" + hashOfConfig(linesToDelete) + " done")

    if versionCompiles:
        logWorkingConfig(linesToDelete)
       

        for nextDeletionCandidate in remainingLines:
            largerSet = frozenset(linesToDelete | frozenset([nextDeletionCandidate]))
            smallerRemaining = frozenset(remainingLines - frozenset([nextDeletionCandidate]))
            doneAlready = False
            #safePrint(str(linesToDelete)+ " is trying to get seenLock")
            with seenLock:
                if largerSet in seenconfig:
                    #safePrint("Not adding " + str(largerSet)+ "/" + hashOfConfig(largerSet) + " to queue, because it was already in seen configs")
                    #doneAlready = True                                                         USEFUL??
                    break
            #safePrint(str(linesToDelete)+ " is trying to get goodconfiglock")
            with goodConfigLock:
                for goodconfig in goodconfigs:
                    if largerSet <= goodconfig:
                        #doneAlready = True
                        #safePrint("Not adding " + str(largerSet)+ "/" + hashOfConfig(largerSet) + " to queue, because " + str(goodconfig)+ "/" + hashOfConfig(goodconfig) + " is among working configs")
                        break
            if not doneAlready:
                queueTask(largerSet,smallerRemaining)
    safePrint("Executor for " + str(linesToDelete)+ "/" + hashOfConfig(linesToDelete) + " done")


def queueTask(startset, remainingset):
    with seenLock:
        seenconfig.add(startset)
    q.put((startset, remainingset),True)
    #safePrint("Added " + str(startset)+ "/" + hashOfConfig(startset) + " to queue")


def getThreadpoolStatistics():
    done = 0
    exceptions = 0
    running = 0
    other = 0
    with futureLock:
        futureCopy = list(futures)
    finished = []
    workingOn = []
    inQueue = []
    for lineset,fut in futureCopy:
        if fut.done():
            done +=1
            if fut.exception() != None:
                exceptions += 1
            else:
                finished.append(lineset)
        else:
            if fut.running():
                 running += 1
                 workingOn.append(lineset)
            else:
                other += 1
                inQueue.append(lineset)
    return (done,exceptions,running,other,finished,workingOn,inQueue)
    
def printFutureStatisticsThread():
    while True:
        global outputFileCounter
        outputFileCounter += 1
        time.sleep(STATISTICS_INTERVAL_SECONDS)
        done,exceptions,running,other,finished,workingOn,inQueue = getThreadpoolStatistics()
        safePrint("Statistics: {0} done (including {3} exceptions), {1} running, {2} remaining".format(done,running,other, exceptions) + "\nFinished: " + str(finished) + "\nWorking on: "+ str(workingOn) +"\nIn Queue: " + str(inQueue))
        with goodConfigLock, open(OUTPUT_FILE + "_" + str(outputFileCounter) + ".txt","w") as f:
            goodconfigswithsize = [(len(s),s) for s in goodconfigs  ]
            goodconfigswithsize = sorted(goodconfigswithsize)
            for goodsetwithsize in goodconfigswithsize:
                goodset = goodsetwithsize[1]
                for line in sorted(goodset):
                    f.write(str(line) + ",")
                f.write("(file " + hashOfConfig(goodset) + ")\n")
        
    


def run():    
    f = open(BASE_FILE_PATH)
    candidates = sorted(determineDeletionCandidates(f))
    safePrint(str(candidates))
    safePrint("Overall lines: " + str(len(candidates)))
    pool.submit(printFutureStatisticsThread)

    queueTask(frozenset([]), frozenset(candidates))


    while(True):
        done,exceptions,running,other,finished,workingOn,inQueue = getThreadpoolStatistics()
        if running < WORKER_THREADS:
            nextSets = q.get(True)
            startset=nextSets[0]
            remainingset=nextSets[1]
            fut = pool.submit(execute, startset, remainingset)
            with futureLock:
                futures.append((startset,fut))
        time.sleep(QUEUE_POLL_INTERVALL_SECONDS)
        #safePrint("Submitted: " + str(startset)+ "/" + hashOfConfig(startset))
