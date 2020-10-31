/*//////////////////////////////////////////////////////////////////////////
// MACH2Ktile.cpp
// Karen Thurston
// CS-600 dissertation research
// Term: Spring and summer 2020
// Updated: August 15, 2020
// Description >>
// *** Program Purpose
//      Summarize GeoLife GPS traces
//      Captures locations at rest, not routes of travel. A very small
//      percentage of someone's day is spent traveling, not worth noting although
//      future work could investigate public transportation as a location that moves (use Wi-Fi).
// *** Program Functions
// 1)	Open a daily GPS trace file from input parameter argv[1]
// 2)   Create and open a daily summary GPS file from input parameter argv[1]
// 3)	Read the first seven daily GPS trace records and throw away (header info, don't need)
// 4)	Read input files beginning with the seventh record
// 5)   Save the time stamp and the geo coordinates for the first location to track from the seventh record
// 6)	While not EOF, read a daily GPS trace record
// 7)  If still within a distance limit (in future: the same hour of day (HOD), and day of week (DOW))
// 8)	If the current record is not within the same OpenStreetMaps tile (base on configured Zoom level) AND
//      If current record time stamp is greater than or equal to the trace interval of 3600 seconds (1 hour)
//        then first look for the same location (tile coordinates) already in MACH2k.txt
//         If the record already exists, add 1 to the frequency
//                  and duration of time in the same location.
//         else write a new record to the MACH2k.txt file with a frequency of 1
// 9)   Close daily GPS input trace file if end of file
// 10)   Write MACH2K records in memory to output file
// 11)   Add to MACH2k output file for each day of GPS traces.
// 12)   Sort MACH2k outputfile by largest frequency and duration then by hour of the day
// 13)  Create a summary record for each subject to summarize all the days of GPS traces into one record for
//      calculating MACH-T value and for calculating population averages and standard deviations.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////*/
#include <cmath>
//#include <ctime>                  // not used currently
#include <fstream>
#include <iomanip>
#include <iostream>
#include <math.h>
#include <sstream>
#include <stdio.h>
#include <stdlib.h>
#include <string>
//#include <time.h>                 // not used currently

//https://nssdc.gsfc.nasa.gov/planetary/factsheet/earthfact.html uses 6378.137 equatorial radius, and 6356.752 polar
#define earthRadiusKm 6371.0
#define PI 3.1415926

using namespace std;

ifstream inFile;                    //GPS trace file input
ifstream inFileM2K;                 //first test if MACH2K.txt already exists to read records

ofstream outFileM2K;                //open MACH2K.txt for writing after testing if it exists for read

double machTrust = 0.0;              // Trust value between 0 and 1
const int MAX_MACH_REC_CNT = 1000;   // Static array size is adequate for now, may make dynamic on next version
double totDaysCnt, totHrsCnt, totLocsCnt, qualLocsCnt, totQualDura, totQualDaysCnt = 0.0; // Totals for MACH2K header record
bool totQualDaysCntUpdate = false; // to determine if input file had at least one qualifying location/duration
string totDaysCntStr, totHrsCntStr, totLocsCntStr, qualLocsCntStr, totQualDuraStr, totQualDaysCntStr;
string minXtileStr, minYtileStr, maxXtileStr, maxYtileStr;
string firstDateTime, lastDateTime;
string fileNameDateTime, fileZoomLevel, fileDuration;
int dow;                            // dow=Day of Week, 0-6, Sunday=0
//string moy;                         // moy=month of year, 1-12
// Standard time variables for converting input date string to a day of the week (same date for every record in input)
struct tm timeDate;
time_t t;

// struct to hold the information in each input trace record
struct traceStruct
{
    string  latitude,   // latitude
    longitude,          // longitude
    zero,               // always "0"
    altitude,           // altitude
    dayNum,             // number of days plus fractional part since 12/30/1899
    YYYYMMDD,           // formatted date
    HHMMSS;             // formatted time
};
struct mach2kStruct     // Discuss how changing distance factor argv[3] affects mach2k.txt reliability
{
    // It may depend on population/building density in a given geo area
    // Probably should define a header record to save run time parameters
    string  xTile,       // from longitude
    yTile,               // from latitude
    hour,                // hour of day at location
    dow,                 // day of week at location
//    mo,                // month at location
    freq,                // number of times at location for minimum duration
    dura,                // cumulative hours at location
    traceCnt,            // cumulative trace pings at location
    firstYYYYMMDD,       // first date at location
    lastYYYYMMDD;        // last date at location
    //More dense cities = smaller distance factor?
};                                   // What is relationship of pop density to distance factor?
mach2kStruct mach2kRec[MAX_MACH_REC_CNT];     // Up to 24 different hours of the day for 5 different locations

// Prototypes
int dayOfWeek(int d, int m, int y);
double deg2rad(double deg);
double distanceEarth(double latFirstLoc, double lonFirstLoc, double latSecLoc, double lonSecLoc);
double rad2deg(double rad);
void selectionSort(mach2kStruct mach2kRec[], int machRecCnt);

int main(int argc, char *argv[])
{
    int          machRecCnt = 0;
    traceStruct  traceRec;
    traceStruct  saveTraceRec;
    // Will multiply by 7 (840 total) when adding days of week
    // for now default to dow = 1, allowing for diff months, *12 = 10,080 recs
    // May want to use linked list to avoid 10,080 recs of memory if not
    // using all of them, although that's still a small amount of memory
//    string mach2kHH[MAX_MACH_REC_CNT];               // Hour values for comparing with traceRec values
//    string mach2kDOW[MAX_MACH_REC_CNT];              // dow values for comparing with traceRec values
    int    mach2kFreq = 0;          // Number of different times subject is in qualifying location
    int    mach2kTraceCnt = 0;      // Number of traces for a qualifying location, high value=high confidence in trust value
    double mach2kDura = 0.0;        // Duration of time in seconds in one location
    string junkRec;                 // read first 6 GPS trace header recs, don't write to output
    string traceHH, saveTraceHH;    // string hour values from trace files (HH from HHMMSS)
    istringstream issConverter;     // for converting strings to ints
    double  saveTime, currTime, duraTime = 0.0;  // input record time in seconds for comparison/calculation
    int    requiredTraceInterval = 600;     // Default to 10 minutes, will parameterize in future
    double maxTraceInterval = 0.0;     // Time interval between trace records, save longest interval for header record
    string maxTraceIntervalStr;        // String to read from MACH2K file header record
    string maxTraceIntervalHHMMSS;     // Save the time of day when longest interval ended
    double minTraceInterval = 3600.0;  // Smallest trace interval, set a large value (1 hour) so it will decrease
    string minTraceIntervalStr;
    int    qualTraceCnt = 0;           // Count traces during qualifying locations to prevent spoofing
    int    totQualTraceCnt = 0;        // Total traces in qualified locations (for duraTime minimum)
    string totQualTraceCntStr;
    double totTraceInterval = 0.0;     // Total of all trace intervals
    string totTraceIntervalStr;
    int    traceRecCnt = 0;         // Number of trace records for a subject
    string traceRecCntStr;
    double saveLat = 0.0;           // saved location latitude center point
    double saveLon = 0.0;           // saved location longitude center point
    double currLat = 0.0;
    double currLon = 0.0;

    double numTiles = 0.0;        // number of tiles at zoom level = 2^n
    int xTileSave, yTileSave;
    int xTileCurr, yTileCurr;
    int minXtile = 99999999;
    int minYtile = 99999999;
    int maxXtile = 0;
    int maxYtile = 0;
    double lat_rad;                  // Latitude in radians


//    cout << "About to do intial parameter count check" << endl;

    /** Get input parameter count **/
    if (argc < 5)
    {
        cout << "Usage: MACH2K [YYYYMMDDHHMMSS.plt] [3-digit userid]> [zoom level(1-21)] [secs. in place (900-3600)]"
             << endl;   // If there are less than five arguments, stop the program
        exit(1);
    }

    /** Command line argv[3], to compare trace locations to saved mach2k.txt locations **/
    int     zoomLevel = atof(argv[3]);       // tileLength below is based on zoom level 16 only
    double  tileLength = 0.469;              // Future: Calculate tileLength based on zoom level and latitude

    numTiles = pow(2,zoomLevel);
    /** Command line argv[4], to test for time in one place/location **/
    /** !!! May want to restrict writing records of diff. duration requirements in same file !!! **/
    /** May want to create header record with runtime parameters to ensure invalid combinations  **/
    /** Seems like it's okay to add to a file using longer time requirements, but not shorter    **/
    double  timeInPlace = atol(argv[4])/(24.0*60.0*60.0);   // argv[4] in seconds, 3600sec. = 1hr., convert to fraction of day

    inFile.open(argv[1]);       // Open a GPS trace file
    if (!inFile)                // Open a GPS trace file
    {
        cout << "Cannot open input file" << argv[1] << endl; // If there are less than two arguments, then stop the program
        exit(2);
    }

    cout << "input name=" << argv[1] << endl;

    /** Get firstDateTime from input file name in case no existing MACH2k.txt file **/
    firstDateTime = argv[1];
    firstDateTime = firstDateTime.substr(0,14);
    lastDateTime = firstDateTime;                   // Current file is last date if it passes validation (or else exit(6)
    cout << "firstDateTime=" << firstDateTime << endl;

    /** Save as fileNameDateTime in case existing MACH2k.txt file has a different firstDateTime **/
    fileNameDateTime = firstDateTime;
    cout << "fileNameDateTime=" << fileNameDateTime << endl;

    /** Try to open an existing MACH2K.txt file from input parameter argv[2]: ###_MACH2K.txt **/
    string outName = argv[2];      // argv[2] is the acct# of person using the device
    outName.append("_MACH2K.txt");
    inFileM2K.open(outName);  // open MACH2K as an ifstream file for reading first, to see if it exists

    /** Future enhancement here: MACH2k.txt can have "seeded" records to determine trust                             **/
    /** first date = date of first match when frequency value is currently zero or negative? to indicate seed value  **/
    if (inFileM2K) // skip reading if no existing MACH2K.txt file
    {
        getline(inFileM2K, junkRec); // Get first record with column headings
        if (junkRec.substr(0,5) != "xTile")
        {
            cout << "First 5 bytes of MACH2K header rec#1=" << junkRec.substr(0,5) << endl;
            cout << "Invalid MACH2K header record. First record must begin with 'xTile'." << endl;
            exit(3);
        }

        /** Get 2nd record distance and duration parameters **/
        getline(inFileM2K, junkRec, '=');
        getline(inFileM2K, fileZoomLevel, ',');  // Need to change to zoom level of 21
        getline(inFileM2K, junkRec, '=');
        getline(inFileM2K, fileDuration, ',');
        getline(inFileM2K, junkRec);          // read remaining record to set up to read next record

        cout << "File distance=" << fileZoomLevel << ", Zoom level parameter=" << argv[3] << endl;
        cout << "File duration=" << fileDuration << ", Duration parameter=" << argv[4] << endl;
        if (fileZoomLevel != argv[3])
        {
            cout << "Existing MACH2K file zoom level of "
                 << fileZoomLevel << " must equal input distance limit of " << argv[3] << "." << endl;
            exit(4);
        }
        if (fileDuration != argv[4])
        {
            cout << "Existing MACH2K file time duration of "
                 << fileDuration << "must equal input time duration of " << argv[4] << " seconds." << endl;
            exit(5);
        }
        getline(inFileM2K, junkRec);      // Skip third record, just headings for summary data
        getline(inFileM2K, firstDateTime, ','); // Get fourth record with totals (convert to integers for accumulating)
        getline(inFileM2K, lastDateTime, ',');
        getline(inFileM2K, totDaysCntStr, ',');
        getline(inFileM2K, totHrsCntStr, ',');
        getline(inFileM2K, totLocsCntStr, ',');
        getline(inFileM2K, qualLocsCntStr,',');
        getline(inFileM2K, totQualDuraStr,',');
        getline(inFileM2K, totQualDaysCntStr, ',');
        getline(inFileM2K, junkRec, ',');  // skip percentage field, will calculate at end
        getline(inFileM2K, minXtileStr,',');
        getline(inFileM2K, minYtileStr,',');
        getline(inFileM2K, maxXtileStr,',');
        getline(inFileM2K, maxYtileStr, ',');
        getline(inFileM2K, junkRec,',');    // skip #1 loc%, calculate at end
        getline(inFileM2K, junkRec,',');    // skip #2 loc%, calculate at end
        getline(inFileM2K, junkRec,',');    // skip #3 loc%, calculate at end
        getline(inFileM2K, junkRec,',');    // skip #4 loc%, calculate at end
        getline(inFileM2K, junkRec,',');    // skip #5 loc%, calculate at end
        getline(inFileM2K, junkRec,',');    // skip #6 loc%, calculate at end
        getline(inFileM2K, junkRec, ',');   // skip subject, Filename check covers that
        getline(inFileM2K, junkRec,',');    // skip next 9 fields: QH/Qdays to TRUST
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, junkRec,',');
        getline(inFileM2K, traceRecCntStr,',');
        getline(inFileM2K, maxTraceIntervalStr,',');
        getline(inFileM2K, maxTraceIntervalHHMMSS,',');
        getline(inFileM2K, minTraceIntervalStr,',');
        getline(inFileM2K, totTraceIntervalStr,',');
        getline(inFileM2K, junkRec,',');           // ignore average trace interval, will recalculate
        getline(inFileM2K, junkRec,',');           // ignore traces per day, will recalculate
        getline(inFileM2K, totQualTraceCntStr);

        totDaysCnt = stof(totDaysCntStr);
        totHrsCnt = stof(totHrsCntStr);
        totLocsCnt = stof(totLocsCntStr);
        qualLocsCnt = stof(qualLocsCntStr);     //Number of locations qualifying for minimum duration time
        totQualDura = stof(totQualDuraStr);     //Number of hours qualifying for minimum duration time
        totQualDaysCnt = stof(totQualDaysCntStr); //Number of days with at least one qualifying location/duration
        minXtile = stoi(minXtileStr);
        minYtile = stoi(minYtileStr);
        maxXtile = stoi(maxXtileStr);
        maxYtile = stoi(maxYtileStr);
        traceRecCnt = stoi(traceRecCntStr);
        maxTraceInterval = stof(maxTraceIntervalStr)/(24.0*60.0*60.0); // convert seconds to days
        minTraceInterval = stof(minTraceIntervalStr);                   // don't convert to days, too small
        totTraceInterval = stof(totTraceIntervalStr)/(24.0*60.0*60.0); // total elapsed time of all traces
        totQualTraceCnt = stoi(totQualTraceCntStr);

    cout << "Reading: traceRecCnt=" << traceRecCnt
         << ",maxTraceInterval=" << maxTraceInterval*24.0*60.0*60.0
         << "minTraceInterval=" << minTraceInterval
         << ",totTraceInterval="<< totTraceInterval*24.0*60.0*60.0
         << ",Traces per day=" << (traceRecCnt/totDaysCnt)
         << ",Avg. Trace=" << (totTraceInterval*24.0*60.0*60.0)/((traceRecCnt*1.0)-totDaysCnt) << endl;
        cout << "M2K read: minXtile=" << minXtile << ",minYtile=" << minYtile << ",maxXtile=" << maxXtile
             << ",maxYtile=" << maxYtile << endl;
        cout << "FileNameDateTime=" << fileNameDateTime << ",lastDateTime=" << lastDateTime << endl;
        /** If current input file date is same or earlier than the last date in MACH2K file, exit, don't double count **/
        if ( fileNameDateTime <= lastDateTime)
        {
            cout << "Trace file cannot be earlier or the same date as the latest processed file date." << endl;
            exit(6);
        }

    if (qualLocsCnt > 0)
    {
    while (getline(inFileM2K, mach2kRec[machRecCnt].xTile, ',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].yTile, ',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].hour, ',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].dow, ',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].freq,',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].dura,',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].traceCnt,',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].firstYYYYMMDD, ',') &&
                getline(inFileM2K, mach2kRec[machRecCnt].lastYYYYMMDD) &&
                (machRecCnt < MAX_MACH_REC_CNT))
        {
            if (machRecCnt == MAX_MACH_REC_CNT)
            {
                cout << "Maximum records exceeded in input MACH2K file." << endl;  //File must have been altered manually
                exit (7);
            }
            else
                machRecCnt += 1;
        } // while not eof
    } // if (qualLocsCnt > 0)

    if (machRecCnt != qualLocsCnt)
    {
        cout << "Mach record count error" << endl;
        exit (8);
    }
    // Close the existing MACH2K file and make a backup copy
    inFileM2K.close();
    string temp, temp2;
    temp = outName + ".bak";
    temp2 = "del " + temp;            // delete existing .bak file if it exists
    system (temp2.c_str());
    temp2 = "copy " + outName + " " + temp;
    system (temp2.c_str());          // make backup copy first before creating new file

    }   // mach2k.txt file had at least one record but no more than MAX

    outFileM2K.open(outName);  // create and open MACH2K file for writing (erases old file)
    if (!outFileM2K)
    {
        cout << "Error creating and opening output file " << outName << endl;
        exit(9);
    }


    /** Skip past the first six daily GPS trace header records **/
    for (int i=0; i<6; i++)
    {
        getline(inFile, junkRec);
    } // for i<6

    /** Read the first input record **/
    if (inFile.eof())
    {
        exit(10);
        cout << "Input " << argv[1] << " has no trace records." << endl;
    }
    else
    {
        // Read first input trace file record
        // readInputTrace(&inFile, traceRec);
        getline(inFile, saveTraceRec.latitude, ',');
        getline(inFile, saveTraceRec.longitude, ',');
        getline(inFile, junkRec, ',');
        getline(inFile, junkRec, ',');
        getline(inFile, saveTraceRec.dayNum, ',');
        getline(inFile, saveTraceRec.YYYYMMDD, ',');
        getline(inFile, saveTraceRec.HHMMSS);
 //       cout << "traceRec.latitude=" << traceRec.latitude << endl;
 //       cout << "traceRec.longitude=" << traceRec.longitude << endl;

        traceRecCnt += 1;
        qualTraceCnt += 1;

        /** Get day of week (dow) and month of year (moy) from first record; stays same for the whole file **/
        dow=dayOfWeek(stoi((saveTraceRec.YYYYMMDD).substr(7,2)),
                      stoi((saveTraceRec.YYYYMMDD).substr(5,2)),
                      stoi((saveTraceRec.YYYYMMDD).substr(0,4)));

        /** Save the first time stamp for comparing **/
        issConverter.clear();
        issConverter.str(saveTraceRec.dayNum);
        issConverter >> saveTime;
        duraTime = 0.0;  // initialize to begin duration accumulation

        /** Save the first hour of the day value **/
        traceHH = saveTraceRec.HHMMSS;
        saveTraceHH = saveTraceHH.substr(0,2);

        /** Save the first location for comparing **/
        issConverter.clear();
        issConverter.str(saveTraceRec.latitude + ' ' + saveTraceRec.longitude);
        issConverter >> saveLat;
        issConverter >> saveLon;

        /** Calculate xTileSave,yTileSave coordinates **/
        xTileSave = numTiles * ((saveLon + 180) / 360);
        lat_rad = deg2rad(saveLat);
        yTileSave = (numTiles * (1 - (log(tan(lat_rad) + 1/cos(lat_rad)) / PI)) / 2);

        cout << "1) xTileSave=" << xTileSave << ", yTileSave=" << yTileSave << endl;

    }
        /** Read records from the GPS trace input file until location **/
        /** changes to a new xTile,yTile coordinate, then look to see how much time has passed **/
        while
            (getline(inFile, traceRec.latitude, ',') &&
            getline(inFile, traceRec.longitude, ',') &&
            getline(inFile, junkRec, ',') &&
            getline(inFile, junkRec, ',') &&
            getline(inFile, traceRec.dayNum, ',') &&
            getline(inFile, traceRec.YYYYMMDD, ',') &&
            getline(inFile, traceRec.HHMMSS))
        {

            /**   Check for day changing, if so, stop processing this file, should only include one day **/
            /**   Get day of week (dow) and month of year (moy) from first record; stays same for the whole file **/
            if (traceRec.YYYYMMDD != saveTraceRec.YYYYMMDD)
            {
                cout << "New day, break!" << endl;
                break;

            }

            /**     Convert string geo locations in trace file to double values for comparison **/
            issConverter.clear();
            issConverter.str(traceRec.latitude + ' ' + traceRec.longitude);
            issConverter >> currLat;
            issConverter >> currLon;

            /** Calculate xTile,yTile coordinates **/
            xTileCurr = numTiles * ((currLon + 180) / 360);
            lat_rad = deg2rad(currLat);
            yTileCurr = (numTiles * (1 - (log(tan(lat_rad) + 1/cos(lat_rad)) / PI)) / 2);

            cout << "xTileCurr=" << xTileCurr << ", yTileCurr=" << yTileCurr << endl;

            issConverter.clear();
            issConverter.str(traceRec.dayNum);
            issConverter >> currTime;

            if (
                (((currTime - saveTime)*24.0*60.0*60.0) <= requiredTraceInterval) && // 10 minute goal interval max in same tile
                (xTileCurr == xTileSave) &&                       // Don't accumulate time if a new location
                (yTileCurr == yTileSave)
               )
                duraTime += currTime - saveTime;         // add time difference since last log record to accumulated time

            /** Get trace intervals for max, min, and average **/
            totTraceInterval += (currTime - saveTime);        // Get total intervals added together to divide by traceCnt @EOF

            cout << "totTraceInterval=" << totTraceInterval << endl;

            if ((currTime - saveTime) > maxTraceInterval)
            {
                maxTraceInterval = currTime - saveTime;    // keep track of longest interval
                maxTraceIntervalHHMMSS = traceRec.HHMMSS;
            cout << "After increase, maxTraceInterval=" << maxTraceInterval << endl;
            }

            if (
                (((currTime - saveTime)*24.0*60.0*60.0) < minTraceInterval) &&
                ((currTime - saveTime)*24.0*60.0*60.0 > 0)
                )                 // Ignore trace intervals of zero
            {
                minTraceInterval = (currTime - saveTime)*24.0*60.0*60.0;    // keep track of shortest interval in seconds
                cout << "After decrease, minTraceInterval=" << minTraceInterval << endl;
            }

            /** increment total hours accumulator for all traces, not just qualifying locations **/
            totHrsCnt += (currTime - saveTime) * 24;     // change from days to hours

            cout << "totHrsCnt=" << totHrsCnt << ",first duraTime=" << duraTime << endl;

            if (
                ((currTime - saveTime) > 0) ||        // Don't count trace records in same tile w/same time stamp
                (xTileCurr != xTileSave) ||           // Unknown why duplicate time stamps, possible airplane travel
                (yTileCurr != yTileSave)
                )
                {
                    traceRecCnt += 1;
                    qualTraceCnt += 1;
                }

            /**  Control break if new tile coordinates  **/
            if ((xTileCurr != xTileSave) || (yTileCurr != yTileSave))
            {

            /** increment total location changes counter if changed location regardless of how much time in location **/
            /** ISSUE: What if sampling rate is 1 second and moving very fast? Would skew towards more locations **/
            /** OPTION: Fast moving nodes should be trusted less? Poor options for network communication too. **/
                totLocsCnt +=1;                 // increment location count whether it is saved or not

            cout << "duraTime=" << duraTime << endl;
                /** Has this location accumulated enough time (duraTime) to be stored in MACH2k.txt file? **/
                if (duraTime >= timeInPlace)
                {
        cout << "duraTime > timeInPlace" << endl;
        cout << "xTileSave=" << xTileSave << ", yTileSave=" << yTileSave << ", hour=" << saveTraceHH << ", dow=" << dow << endl;
                qualTraceCnt +=1;
        cout << "qualTraceCnt=" << qualTraceCnt << endl;
                totQualDaysCntUpdate = true; // so we can increment the totQualDaysCnt value for header record
            /** Save smallest and largest x,y tiles for qualifying tiles for output file header for range of locations **/
                if (xTileSave < minXtile)
                    minXtile = xTileSave;
                if (yTileSave < minYtile)
                    minYtile = yTileSave;
                if (xTileSave > maxXtile)
                    maxXtile = xTileSave;
                if (yTileSave > maxYtile)
                    maxYtile = yTileSave;

            /** increment duration if changed location qualifies for time in location **/
                totQualDura += duraTime * 24.0;

                /** Search mach2kRec for same tile coordinates      **/
                /** at same hour, dow and month or write new record **/
                bool foundMachRec = false;              // Initialize flag for any match in MACH2K array
                int bestMachRecIdx = -1;                // Initialize best location match in MACH2K array

                for (int i=0; i<machRecCnt; i++)
                {
                    issConverter.clear();
                    issConverter.str(mach2kRec[i].dura);    // duration in hours
                    issConverter >> mach2kDura;

                    /** Begin comparing MACH2K record locations to current input file location for FIRST match **/
                    if ((to_string(xTileSave) == mach2kRec[i].xTile) &&
                        (to_string(yTileSave) == mach2kRec[i].yTile))
/**                         &&
                        (saveTraceHH == mach2kRec[i].hour) &&
                        (to_string(dow) == mach2kRec[i].dow)) **/
//                        (moy == mach2kRec[i].mo))
                    {
            cout << "machRecCnt=" << machRecCnt << ",i=" << i << ",mach2kRec[i].xTile=" << mach2kRec[i].xTile << ",mach2kRec[i].yTile="
                 << mach2kRec[i].yTile << endl;
                        bestMachRecIdx = i;
                        i=machRecCnt;           // stop at the first find, by design is the only find
                    }
                } // end for loop looking for existing MACH2K record
                cout << "bestMachRecIdx=" << bestMachRecIdx << endl;

                /** Update existing MACH2K record with same xTile,yTile coordinates **/
                if (bestMachRecIdx != -1)
                {
                    issConverter.clear();
                    issConverter.str(mach2kRec[bestMachRecIdx].freq);
                    issConverter >> mach2kFreq;
                    mach2kFreq += 1;

                    mach2kDura += duraTime * 24.0; // add duration time in hrs to existing value

                    if (mach2kFreq < 10)
                        mach2kRec[bestMachRecIdx].freq = "00" + to_string(mach2kFreq);
                    else
                        if (mach2kFreq < 100)
                            mach2kRec[bestMachRecIdx].freq = "0" + to_string(mach2kFreq);
                        else
                            if (mach2kFreq < 1000)
                                mach2kRec[bestMachRecIdx].freq = to_string(mach2kFreq);

                    if (mach2kDura < 10.0)
                        mach2kRec[bestMachRecIdx].dura = "00" + to_string(mach2kDura);
                    else
                        if (mach2kDura < 100.0)
                            mach2kRec[bestMachRecIdx].dura = '0' + to_string(mach2kDura);
                        else
                            if (mach2kDura < 1000.0)
                                mach2kRec[bestMachRecIdx].dura = to_string(mach2kDura);

                    cout << "mach2kRec.dura=" << mach2kRec[bestMachRecIdx].dura << endl;
//                    mach2kRec[bestMachRecIdx].hour = saveTraceHH;
                    mach2kRec[bestMachRecIdx].hour = "99";

                    cout << "Before update, mach2kRec[bestMachRecIdx].traceCnt=" << mach2kRec[bestMachRecIdx].traceCnt << endl;

                    issConverter.clear();
                    issConverter.str(mach2kRec[bestMachRecIdx].traceCnt);
                    issConverter >> mach2kTraceCnt;
                    cout << "Before update, mach2kTraceCnt=" << mach2kTraceCnt << endl;
                    mach2kTraceCnt += qualTraceCnt;
                    totQualTraceCnt += qualTraceCnt;

                    cout << "Updating MACH2K rec, mach2kTraceCnt=" << mach2kTraceCnt << ",qualTraceCnt=" << qualTraceCnt << endl;
                    mach2kRec[bestMachRecIdx].traceCnt = to_string(mach2kTraceCnt); //No need for leading 0's, not sorting

                    cout << "After update, mach2kRec[bestMachRecIdx].traceCnt=" << mach2kRec[bestMachRecIdx].traceCnt << endl;

                    qualTraceCnt = 0;

                    mach2kRec[bestMachRecIdx].lastYYYYMMDD = saveTraceRec.YYYYMMDD;
                    foundMachRec = true;
                    duraTime = 0.0;
                } // updated existing MACH2K record

                /** Create new MACH2K record if still room in memory array of records **/
                if (!foundMachRec)
                {
                    if (machRecCnt < MAX_MACH_REC_CNT - 1)
                    {
                        mach2kRec[machRecCnt].xTile = to_string(xTileSave);
                        mach2kRec[machRecCnt].yTile = to_string(yTileSave);

        cout << "NEW REC: machRecCnt=" << machRecCnt << ",mach2kRec[machRecCnt].xTile=" << mach2kRec[machRecCnt].xTile
             << ", mach2kRec[machRecCnt].yTile=" << mach2kRec[machRecCnt].yTile << endl;

//                        mach2kRec[machRecCnt].hour = saveTraceHH;
                        mach2kRec[machRecCnt].hour = "99";
//                        mach2kRec[machRecCnt].dow = to_string(dow);
                        mach2kRec[machRecCnt].dow = '9';
                        mach2kRec[machRecCnt].freq = "001";
                        if ((duraTime*24) < 10.0)
                            mach2kRec[machRecCnt].dura = "00" + to_string(duraTime*24);
                        else
                            if ((duraTime*24) < 100.0)
                                mach2kRec[machRecCnt].dura = '0' + to_string(duraTime*24);
                            else
                                if ((duraTime*24) < 1000.0)
                                    mach2kRec[machRecCnt].dura = to_string(duraTime*24);
                    cout << "duraTime*24=" << duraTime*24 << ", mach2kRec.dura=" << mach2kRec[machRecCnt].dura << endl;
                    //getchar();

                    cout << "New MACH2K rec, qualTraceCnt=" << qualTraceCnt << ",to_string=" << to_string(qualTraceCnt) << endl;

                        mach2kRec[machRecCnt].traceCnt = to_string(qualTraceCnt);
                        totQualTraceCnt += qualTraceCnt;

                    cout << "After to_string, mach2kRec[machRecCnt].traceCnt=" << mach2kRec[machRecCnt].traceCnt << endl;

                        qualTraceCnt = 0;

                        mach2kRec[machRecCnt].firstYYYYMMDD = saveTraceRec.YYYYMMDD;
                        mach2kRec[machRecCnt].lastYYYYMMDD = saveTraceRec.YYYYMMDD;
                    cout << "mach2kRec[machRecCnt].firstYYYYMMDD=" << mach2kRec[machRecCnt].firstYYYYMMDD << endl;
                    cout << "mach2kRec[machRecCnt].lastYYYYMMDD=" << mach2kRec[machRecCnt].lastYYYYMMDD << endl;
                        machRecCnt += 1;
                    cout << "updated machRecCnt=" << machRecCnt << endl;
                        duraTime = 0.0;
                    }
                    else
                    {
                    cout << "Error: More than maximum, " << MAX_MACH_REC_CNT << ' '<< argv[2] << "MACH2K.txt records." << endl;
                    exit(11);
                    }
                } // end if no record for this location yet in MACH2K file

                } // end if at least minimum time in same location after reading first record in changed location
            else
                duraTime = 0.0;     // reset duration if change in location or below threshhold timeInPlace
                qualTraceCnt = 0;    // also reset qualTraceCnt

            cout << "got to end of new location or trace interval 60 or more seconds" << endl;
            } // end of new location

        /** Save new trace record to compare to next trace records and to MACH2k.txt recs **/
        saveTraceRec.latitude = traceRec.latitude;
        saveTraceRec.longitude = traceRec.longitude;
        saveTraceRec.dayNum = traceRec.dayNum;
        saveTraceRec.YYYYMMDD = traceRec.YYYYMMDD;
        saveTraceRec.HHMMSS = traceRec.HHMMSS;

        traceHH = traceRec.HHMMSS;
        saveTraceHH = traceHH.substr(0,2);

        /** Save the time stamp from current read for comparing **/
        saveTime = currTime;

        /** Save the location for comparing **/
        saveLat = currLat;
        saveLon = currLon;

        /** Save xTileSave,yTileSave coordinates **/
        xTileSave = xTileCurr;
        yTileSave = yTileCurr;

        cout << "After location break: xTileSave=" << xTileSave << ", yTileSave=" << yTileSave << endl;

    } // while traceFile still has records

    cout << "before testing for more data after EOF, saveTime=" << saveTime << ",currTime=" << currTime << endl;

    if (
        (((currTime - saveTime)*24.0*60.0*60.0) <= requiredTraceInterval) && // 10 minute goal interval max in same tile
        (xTileCurr == xTileSave) &&                       // Don't accumulate time if a new location
        (yTileCurr == yTileSave)
        )
        duraTime += currTime - saveTime;         // add time difference since last log record to accumulated time

    /** Write last record if eligible to be written and if any data since last break in location! **/
    /** Handle situation where all records within one tile, for the whole file (happens at low zoom levels) **/
    if ((saveTime != currTime) || (duraTime >= timeInPlace))  // duraTime will be zero if last record is new location
    {
        /** increment total locations counter if new location regardless of how much time in location **/
        totLocsCnt +=1;                 // increment location count whether it qualifies or not

        totQualDaysCntUpdate = true; // so we can increment the totQualDaysCnt value for header record

        cout << "EOF: duraTime=" << duraTime << endl;
        cout << "EOF: machRecCnt=" << machRecCnt << endl;

        if (duraTime >= timeInPlace)
        {
        cout << "EOF: duraTime > timeInPlace" << endl;
        cout << "xTileSave=" << xTileSave << ", yTileSave=" << yTileSave << ", hour=" << saveTraceHH << ", dow=" << dow << endl;
            qualTraceCnt +=1;
        cout << "qualTraceCnt=" << qualTraceCnt << endl;

        /** Save smallest and largest x,y tiles for qualifying tiles for output file header for range of locations **/
            if (xTileSave < minXtile)
                minXtile = xTileSave;
            if (yTileSave < minYtile)
                minYtile = yTileSave;
            if (xTileSave > maxXtile)
                maxXtile = xTileSave;
            if (yTileSave > maxYtile)
                maxYtile = yTileSave;

        /** increment qualifying location counter and accumulate duration if changed location qualifies for time in location **/
            totQualDura += duraTime * 24.0;

        /** Search mach2kRec for best/closest same location within distanceLimit, **/
        /** at same hour, dow and month or write new record                       **/
            bool foundMachRec = false;              // Initialize flag for any match in MACH2K array
            int bestMachRecIdx = -1;                // Initialize best location match in MACH2K array

            for (int i=0; i<machRecCnt; i++)
            {
                issConverter.clear();
                issConverter.str(mach2kRec[i].dura);    // duration in hours
                issConverter >> mach2kDura;

                /** Begin comparing MACH2K record locations to current input file location for FIRST match **/
                if ((to_string(xTileSave) == mach2kRec[i].xTile) &&
                    (to_string(yTileSave) == mach2kRec[i].yTile))
/**                         &&
                        (saveTraceHH == mach2kRec[i].hour) &&
                        (to_string(dow) == mach2kRec[i].dow)) **/
//                        (moy == mach2kRec[i].mo))
                    {
            cout << "EOF: machRecCnt=" << machRecCnt << ",i=" << i << ",mach2kRec[i].xTile=" << mach2kRec[i].xTile << ",mach2kRec[i].yTile="
                 << mach2kRec[i].yTile << endl;
                        bestMachRecIdx = i;
                        i=machRecCnt; // stop at the first find

                    }
        } // end for loop looking for existing MACH2k record
            cout << "bestMachRecIdx=" << bestMachRecIdx << endl;

            /** Update existing MACH2K record with closest location matching hour/dow **/
            if (bestMachRecIdx != -1)
            {
                issConverter.clear();
                issConverter.str(mach2kRec[bestMachRecIdx].freq);
                issConverter >> mach2kFreq;
                mach2kFreq += 1;

                mach2kDura += duraTime * 24.0; // add duration time in hrs to existing value

                if (mach2kFreq < 10)
                    mach2kRec[bestMachRecIdx].freq = "00" + to_string(mach2kFreq);
                else
                    if (mach2kFreq < 100)
                        mach2kRec[bestMachRecIdx].freq = '0' + to_string(mach2kFreq);
                    else
                        if (mach2kFreq < 1000)
                            mach2kRec[bestMachRecIdx].freq = to_string(mach2kFreq);

                    if (mach2kDura < 10.0)
                        mach2kRec[bestMachRecIdx].dura = "00" + to_string(mach2kDura);
                    else
                        if (mach2kDura < 100.0)
                            mach2kRec[bestMachRecIdx].dura = '0' + to_string(mach2kDura);
                        else
                            if (mach2kDura < 1000.0)
                                mach2kRec[bestMachRecIdx].dura = to_string(mach2kDura);

                   cout << "mach2kDura=" << mach2kDura << ",mach2kRec.dura=" << mach2kRec[bestMachRecIdx].dura << endl;

//                mach2kRec[bestMachRecIdx].hour = saveTraceHH;
                mach2kRec[bestMachRecIdx].hour = "99";

                cout << "Before update, mach2kRec[bestMachRecIdx].traceCnt=" << mach2kRec[bestMachRecIdx].traceCnt << endl;

                issConverter.clear();
                issConverter.str(mach2kRec[bestMachRecIdx].traceCnt);
                issConverter >> mach2kTraceCnt;

                cout << "EOF: Before update, mach2kTraceCnt=" << mach2kTraceCnt << endl;
                mach2kTraceCnt += qualTraceCnt;
                totQualTraceCnt += qualTraceCnt;

                cout << "EOF: Updating MACH2K rec, mach2kTraceCnt=" << mach2kTraceCnt << ",qualTraceCnt=" << qualTraceCnt << endl;

                mach2kRec[bestMachRecIdx].traceCnt = to_string(mach2kTraceCnt); //No need for leading 0's, not sorting
                cout << "EOF: After update, mach2kRec[bestMachRecIdx].traceCnt==" << mach2kRec[bestMachRecIdx].traceCnt << endl;

                qualTraceCnt = 0;

                mach2kRec[bestMachRecIdx].lastYYYYMMDD = saveTraceRec.YYYYMMDD;
                foundMachRec = true;
                duraTime = 0.0;
            } // updated existing MACH2K record

            /** Create new MACH2K record if still room in memory array of records **/
            if (!foundMachRec)
            {
                if (machRecCnt < MAX_MACH_REC_CNT - 1)
                {
                    mach2kRec[machRecCnt].xTile = to_string(xTileSave);
                    mach2kRec[machRecCnt].yTile = to_string(yTileSave);

        cout << "EOF: xTileSave=" << xTileSave << ",yTileSave=" << yTileSave << endl;

//                    mach2kRec[machRecCnt].hour = saveTraceHH;
//                    mach2kRec[machRecCnt].dow = to_string(dow);
                    mach2kRec[machRecCnt].hour = "99";
                    mach2kRec[machRecCnt].dow = '9';
                    mach2kRec[machRecCnt].freq = "001";

                    if ((duraTime*24) < 10.0)
                        mach2kRec[machRecCnt].dura = "00" + to_string(duraTime*24);
                    else
                        if ((duraTime*24) < 100.0)
                            mach2kRec[machRecCnt].dura = '0' + to_string(duraTime*24);
                        else
                            if ((duraTime*24) < 1000.0)
                                mach2kRec[machRecCnt].dura = to_string(duraTime*24);
                    cout << "EOF: duraTime*24=" << duraTime*24 << ",mach2kRec.dura=" << mach2kRec[machRecCnt].dura << endl;
                    //getchar();

                    cout << "New MACH2K rec, qualTraceCnt=" << qualTraceCnt << ",to_string=" << to_string(qualTraceCnt) << endl;

                    mach2kRec[machRecCnt].traceCnt = to_string(qualTraceCnt);
                    cout << "After to_string, mach2kRec[machRecCnt].traceCnt=" << mach2kRec[machRecCnt].traceCnt << endl;

                    totQualTraceCnt += qualTraceCnt;

                    qualTraceCnt = 0;

                    mach2kRec[machRecCnt].firstYYYYMMDD = saveTraceRec.YYYYMMDD;
                    mach2kRec[machRecCnt].lastYYYYMMDD = saveTraceRec.YYYYMMDD;
                    machRecCnt += 1;
                    duraTime = 0.0;
                }
                else
                {
                cout << "Error: More than " << MAX_MACH_REC_CNT << ' '<< argv[2] << "MACH2K.txt records." << endl;
                exit(12);
                }
            } // end if no record for this location yet in MACH2K file
        } // end if at least minimum time in same location after reading first record in changed location
    }// at least some data qualifying for one more MACH2K record

    /** Close daily GPS trace file **/
    inFile.close();

    /** Write MACH2K records, if any, from memory and close MACH2K.txt file **/

    cout << "About to write to MACH2K file, machRecCnt=" << machRecCnt << endl;

    // Sort by duration in descending order
    if (machRecCnt > 1)
        selectionSort(mach2kRec, machRecCnt);

    if (totQualDaysCntUpdate)  // true if this input file had at least one qualifying location/duration
        ++totQualDaysCnt;

    if (minXtile == 999999)
        minXtile = 0;
    // Write file headers with summary info
    outFileM2K << "xTile,yTile,Hour,DOW,Freq,Hours Duration,FirstDate,LastDate\n";
    outFileM2K << "zoom level=" << argv[3] << ", seconds=" << argv[4] << ", version=" << argv[0] << "\n";
    outFileM2K << "1st date/time,Last date/time,Tot days,Tot hrs,Tot locs,Qual locs,"
               << "Tot qual hrs,Tot qual days,Qual hrs/Tot hrs %,Min xTile,Min yTile,Max xTile,Max yTile,"
               << "#1 loc%,#2 loc%,#3 loc%,#4 loc%,#5 loc%,#6 loc%,Subject,"
               << "QH/Qdays,QL/Qdays,QD/TD,QL km^2,QL bound km^2,km^2 Density,QL/TL,QH/TH,TRUST,"
               << "Trace Cnt,Max Interval,Max Interval HHMMSS,Min Interval,Cumm. Trace Secs.,Traces/Day,Avg Interval,"
               << "Tot Qual Trace Cnt\n";

    outFileM2K << firstDateTime << ','                  // 1st date/time
               << fileNameDateTime << ','               // Last date/time
               << ++totDaysCnt << ','                   // Tot days
               << totHrsCnt << ','                      // Tot hrs
               << totLocsCnt << ','                     // Tot locs
               << machRecCnt << ','                     // Qual locs
               << totQualDura << ','                    // Tot qual hrs
               << totQualDaysCnt << ','                 // Tot qual days
               << (totQualDura/totHrsCnt)*100.00 << ','    // Qual hrs/Tot hrs
               << minXtile << ','                       // Min xTile
               << minYtile << ','                       // Min yTile
               << maxXtile << ','                       // Max xTile
               << maxYtile << ',';                      // Max yTile

    // Write the top six location durations (checking to be sure we have five records) to the header
    for (int i=0; i<6; i++)
        if (i >= machRecCnt)
            outFileM2K << 0.00 << ',';
        else
            outFileM2K << (stof(mach2kRec[i].dura)/totQualDura)*100.00 << ','; //#1-#6 loc%

    outFileM2K << argv[2] << ',';                       // Subject

    if (totQualDaysCnt > 0)      // avoid division by zero
        outFileM2K << totQualDura/totQualDaysCnt << ','
                   << machRecCnt/totQualDaysCnt << ',';
    else
        outFileM2K << 0 << ','
                   << 0 << ',';

    outFileM2K << totQualDaysCnt/totDaysCnt << ','
               << machRecCnt*.219961 << ','                                             //QL km^2
               << ((maxXtile-minXtile+1)*tileLength)*((maxYtile-minYtile+1)*tileLength) << ','      //QL bound km^2
               << ((machRecCnt*.219961)/(((maxXtile-minXtile+1.0)*tileLength)*((maxYtile-minYtile+1.0)*tileLength))) << ',' // Density
               << machRecCnt/totLocsCnt << ','
               << totQualDura/totHrsCnt << ',';

    if ((totDaysCnt > 0) &&
        (((maxXtile-minXtile+1)*tileLength)*((maxYtile-minYtile+1)*tileLength) < 1000.0) && // Less than 1000km^2 area
        (machRecCnt > 2))                                                       // Trust = 0 if < 3 locations
    {
        /** Calculate TRUST value, equal weights for each factor for now **/
        machTrust = .1666*((totQualDura/totQualDaysCnt)/2.49) + // divide all terms by observed avg.p + 1 standard deviation
                    .1666*((machRecCnt/totQualDaysCnt)/.93) +
                    .1666*((totQualDaysCnt/totDaysCnt)/.17) +
                    .1666*((machRecCnt/totLocsCnt)/.003) +
                    .1666*((totQualDura/totHrsCnt)/.102) +
                    // QualLocs area in km^2 / QualLocs boundary area in km^2
                    .1666*((machRecCnt*.219961)/(((maxXtile-minXtile+1)*tileLength)*((maxYtile-minYtile+1)*tileLength))/.40);

        if (totDaysCnt < 30)
            machTrust = machTrust * (totDaysCnt/30.0);       // Adjust trust if < 30 total days of data
        outFileM2K << machTrust<< ',';                     // May want to check for at least 30 consecutive days?
    }
    else
        outFileM2K << "0,";        // if no qualifying days yet, TRUST=0

    /** Add Trace Cnt and max, min, total intervals (in seconds) at end of header data **/
    cout << "Writing: traceRecCnt=" << traceRecCnt
         << ",maxTraceInterval=" << maxTraceInterval*24.0*60.0*60.0
         << ", maxTraceIntervalHHMMSS=" << maxTraceIntervalHHMMSS
         << ",minTraceInterval=" << minTraceInterval
         << ",tot Trace Intervals=" << totTraceInterval*24.0*60.0*60.0
         << ", Traces per day=" << (traceRecCnt/totDaysCnt)
         << ",Avg. Trace=" << (totTraceInterval*24.0*60.0*60.0)/((traceRecCnt*1.0)-totDaysCnt) << endl;
    outFileM2K  << traceRecCnt << ','
                << maxTraceInterval*24.0*60.0*60.0 << ','
                << maxTraceIntervalHHMMSS << ','
                << minTraceInterval << ','
                << totTraceInterval*24.0*60.0*60.0 << ','
                << traceRecCnt/totDaysCnt << ','
                << (totTraceInterval*24.0*60.0*60.0)/((traceRecCnt*1.0)-totDaysCnt) << ','
                << totQualTraceCnt << "\n";

    cout << "Before mach2kRec(s) write, machRecCnt=" << machRecCnt << "mach2kRec[0].traceCnt=" << mach2kRec[0].traceCnt << endl;
    /** Write data records **/
    for (int i=0; i<machRecCnt; i++)
        outFileM2K  << mach2kRec[i].xTile << ','
                    << mach2kRec[i].yTile << ','
                    << mach2kRec[i].hour << ','
                    << mach2kRec[i].dow << ','
//                       << mach2kRec[i].mo << ','
                    << mach2kRec[i].freq << ','
                    << mach2kRec[i].dura << ','
                    << mach2kRec[i].traceCnt << ','
                    << mach2kRec[i].firstYYYYMMDD << ','
                    << mach2kRec[i].lastYYYYMMDD << "\n";

    outFileM2K.close();

    return 0;
} // end main

/**
*
* Convert day(d), month(m) and year(y) to a day of week value (0=Sunday)
*   from: https://www.geeksforgeeks.org/find-day-of-the-week-for-a-given-date/
**/
int dayOfWeek(int d, int m, int y)
{
    static int t[] = { 0, 3, 2, 5, 0, 3,
                       5, 1, 4, 6, 2, 4 };
    y -= m < 3;
    return ( y + y / 4 - y / 100 +
             y / 400 + t[m - 1] + d) % 7;
}

/**
*
* This function converts decimal degrees to radians
*
**/
double deg2rad(double deg)
{
    return (deg * 3.1415926 / 180);
}

/**
* From:
* stackoverflow.com/questions/10198985/calculating-the-distance-between-2-latitudes-and-longitudes-that-are-saved-in-a/10205532
* Returns the distance in km between two points on the Earth.
* Direct translation from http://en.wikipedia.org/wiki/Haversine_formula
* Online distance calculator using same formula - http://www.movable-type.co.uk/scripts/latlong.html
* @param lat1d Latitude of the first point in degrees
* @param lon1d Longitude of the first point in degrees
* @param lat2d Latitude of the second point in degrees
* @param lon2d Longitude of the second point in degrees
* @return The distance between the two points in kilometers
*/
double distanceEarth(double lat1d, double lon1d, double lat2d, double lon2d)
{
    double lat1r, lon1r, lat2r, lon2r, u, v;
    lat1r = deg2rad(lat1d);
    lon1r = deg2rad(lon1d);
    lat2r = deg2rad(lat2d);
    lon2r = deg2rad(lon2d);
    u = sin((lat2r - lat1r)/2);
    v = sin((lon2r - lon1r)/2);
    return 2.0 * earthRadiusKm * asin(sqrt(u * u + cos(lat1r) * cos(lat2r) * v * v));
}

/**
*
*  This function converts radians to decimal degrees
*
**/
double rad2deg(double rad)
{
    return (rad * 180 / 3.1415926);
}

/**************************************************************
 *                        selectionSort                       *
 * This function performs an descending-order selection sort   *
 * on array. The parameter size holds the number of elements  *
 * in the array.                                              *
 **************************************************************/
void selectionSort(mach2kStruct mach2kRec[], int size)
{
    double num1, num2;
    int minIndex,swapsMade2 = 0; //all of these will hold a temporary value

    mach2kStruct minValue[1]; // this creates an object to hold temporary object values

	for (int startScan = 0; startScan < (size - 1); startScan++)
	{
		minIndex = startScan;           //the first index starts at 0
		minValue[0] = mach2kRec[startScan];    //the minimum value is the very first number now
		for(int index = startScan + 1; index < size; index++)
		{
		    //these next four lines change the string variables in to usable integer types for comparison
		    stringstream ss(mach2kRec[index].dura);
                ss >> num1;
            stringstream ss1(minValue[0].dura);
                ss1 >>num2;
			if (num1 > num2) //if the number we have is greater than number 2
			{
				minValue[0] = mach2kRec[index]; //we have the current value of index which is now the new temporary value
				minIndex = index;                // temp index is now the number we are on
				swapsMade2++;                    //increment for the swap we just made
			}

      } // moved start all the way to the end of the array
		mach2kRec[minIndex] = mach2kRec[startScan]; // we now change the list to reflect the lowest value we found
		mach2kRec[startScan] = minValue[0];    //the smallest value is added and the loop is repeated

	} // end last scan through array
}
