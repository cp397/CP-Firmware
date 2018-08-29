/////////////////////////////////////////////////////////////////////////////
//! \file comm_discovery.c
//! \brief This file is part of the communications module and handles communication
//! 	protocols while the node is attempting to join a network.
//! \addtogroup Communications
//! @{
//!
//! Chris Porter 3/14
//!
/////////////////////////////////////////////////////////////////////////////

#include <stdint.h>
#include <msp430x54x.h>		//processor reg description */
#include "../time_wisard.h"					//Time routines
#include "comm.h"    			//event MSG module
#include "buz.h"					//Buzzer
#include "adf7020.h"			//radio driver
#include "L2fram.h" 			//Level 2 Fram routines
#include "l2sram.h"  			//disk storage module
#include "misc.h"					//homeless functions
#include "crc.h"					//CRC calculation module
#include "gid.h"					//group ID routines
#include "serial.h"				//serial IO port stuff
#include "rand.h"					//random number generator
#include "task.h"					//Task management module
#include "rts.h" 					//scheduling functions
#include "report.h"				//Logging module
#include "main.h"					// For getting software version
#include "lnkblk.h"				// Link information
#include "contracts.h"

/////////////////// defines //////////////////////
#define MAX_LINKS_PER_SLOT		3



///////////////////   externs    /////////////////////////
extern uchar ucGLOB_myLevel; //senders level +1
extern uint uiGLOB_TotalRTJ_attempts; //counts number of Request to Join attempts

// routing data
extern uint uiNumEdges;
extern S_Edge S_edgeList[MAX_EDGES];

// Freqency sync
extern uchar ucFreqAdjustIndex;


extern volatile union //ucFLAG0_BYTE
{
	uchar byte;
	struct
	{
		unsigned FLG0_BIGSUB_CARRY_BIT :1; //bit 0 ;1=CARRY, 0=NO-CARRY
		unsigned FLG0_BIGSUB_6_BYTE_Z_BIT :1; //bit 1 ;1=all diff 0, 0=otherwise
		unsigned FLG0_BIGSUB_TOP_4_BYTE_Z_BIT :1; //bit 2 ;1=top 4 bytes 0, 0=otherwise
		unsigned FLG0_NOTUSED_3_BIT :1; //bit 3 ;1=SOM2 link exists, 0=none
		//SET:	when any SOM2 links exist
		//CLR: 	when the SOM2 link is lost
		unsigned FLG0_RESET_ALL_TIME_BIT :1; //bit 4 ;1=do time  reset, 0=dont
		//SET:	when RDC4 gets finds first
		//		SOM2.
		//		or
		//		In a hub when it is reset.
		//
		//CLR: 	when vMAIN_computeDispatchTiming()
		//		runs next.
		unsigned FLG0_SERIAL_BINARY_MODE_BIT :1; //bit 5 1=binary mode, 0=text mode
		unsigned FLG0_HAVE_WIZ_GROUP_TIME_BIT :1; //bit 6 1=Wizard group time has
		//        been aquired from a DC4
		//      0=We are using startup time
		unsigned FLG0_NOTUSED7_BIT :1; //bit 7
	} FLAG0_STRUCT;
} ucFLAG0_BYTE;

extern volatile union
{
	uint8 byte;
	struct
	{
		unsigned FLG3_RADIO_ON_BIT :1;
		unsigned FLG3_RADIO_MODE_BIT :1;
		unsigned FLG3_RADIO_PROGRAMMED :1;
		unsigned FLG2_BUTTON_INT_BIT :1; //bit 2 ;1=XMIT, 0=RECEIVE
		unsigned FLG3_LINKSLOT_ALARM :1;
		unsigned FLG3_LPM_DELAY_ALARM :1;
		unsigned FLG3_KEY_PRESSED :1;
		unsigned FLG3_GSV_COM_BIT :1; // 1=GSV com is active 0= GSV com is inactive
	} FLAG3_STRUCT;
} ucFLAG3_BYTE;


//////////////////  variables  /////////////////////////

//! \var ucaLinkSlotTimes[MAX_LINKS_PER_HALFSLOT]
//! \brief This lookup table to provides the reply time based on the random linkslot selected
static const uint ucaLinkSlotTimes[MAX_LINKS_PER_SLOT] =
{ 0x0000, 0x0400, 0x0800 };

static uint16_t uiaLinkSN[MAX_LINKS_PER_SLOT];
static uint8_t  ucLinkSNidx;

// Structure containing discovery modes and settings (Initial state is invalid)
static T_Discovery S_Discovery = {0xFF, 0, 0};

//! \var ulaDiscDuration
//! \brief Durations(in seconds) allowed in each discovery mode
static const ulong ulaDiscDuration[MAXDISCOVERYMODES] = {0, 60, 14400};

/************************** Code starts here *********************************/



///////////////////////////////////////////////////////////////////////////////
//! \brief Builds the request to join message
//!
//! This is the message sent by a child node after it receives a beacon message.
//! It contains the random seed which is a deterministic random number
//! generated to coordinate communication in future slots.
//!
//! \param ulRandomSeed
//! \return none
///////////////////////////////////////////////////////////////////////////////
static void vBuildRequestToJoin(uint8_t* ucMsgBuf, uint32_t ulRandomSeed)
{
    uint8_t ucMsgIndex;
	uint8_t ucEdgeCount;
	uint8_t ucPacketSize;

	REQUIRE(ucMsgBuf);

    // Stuff the message type, flags, number,
	ucMsgBuf[MSG_IDX_ID]     = MSG_ID_REQUEST_TO_JOIN;
	ucMsgBuf[MSG_IDX_FLG]    = 0x20;
	ucMsgBuf[MSG_IDX_NUM_HI] = 0x00;
	ucMsgBuf[MSG_IDX_NUM_LO] = 0x00;

	//Stuff the source address
	vL2FRAM_copySnumLo16ToBytes(&ucMsgBuf[MSG_IDX_ADDR_HI]);

	// Stuff the random seed to schedule future communication
	vMISC_copyUlongIntoBytes(ulRandomSeed, &ucMsgBuf[MSG_IDX_RANDSEED_XI], NO_NOINT);

	ucMsgBuf[MSG_IDX_NUM_EDGES] = uiNumEdges;

	ucMsgIndex = MSG_IDX_EDGE_DISC;

	if (uiNumEdges < (MAX_MSG_SIZE - 0x12))
	{
		// load the routing table
		for (ucEdgeCount = 0; ucEdgeCount < uiNumEdges; ucEdgeCount++)
		{
		    ucMsgBuf[ucMsgIndex++] = (uint8_t) (S_edgeList[ucEdgeCount].m_uiSrc >> 8);
		    ucMsgBuf[ucMsgIndex++] = (uint8_t) S_edgeList[ucEdgeCount].m_uiSrc;
		    ucMsgBuf[ucMsgIndex++] = (uint8_t) (S_edgeList[ucEdgeCount].m_uiDest >> 8);
		    ucMsgBuf[ucMsgIndex++] = (uint8_t) S_edgeList[ucEdgeCount].m_uiDest;
		}

		// stuff message size
		ucMsgBuf[MSG_IDX_LEN] = NET_HDR_SZ + MSG_HDR_SZ + CRC_SZ + (uiNumEdges * sizeof(S_Edge));
	}

	// Get packet len and compute CRC
	ucPacketSize = ucMsgBuf[MSG_IDX_LEN] + NET_HDR_SZ + CRC_SZ;
	ucCRC16_compute_msg_CRC(CRC_FOR_MSG_TO_SEND, ucMsgBuf, ucPacketSize);

} //END: vBuildRequest_to_Join()



///////////////////////////////////////////////////////////////////////////////
//! \brief Builds the beacon message
//!
//! This message is used by parent nodes, including the hub, to advertise
//! possible network connectivity to any listening children.  It contains the
//! time for synchronization as well as group ID and distance in hops from the
//! hub (sourceIDlevel)
//!
///////////////////////////////////////////////////////////////////////////////
static void vBuildBeacon(uint8_t* ucMsgBuf, int32_t lSyncTimeSec)
{
	uint16_t uiSubSeconds;
	uint8_t ucPacketSize;

	REQUIRE(ucMsgBuf);

    // Stuff the message type, flags, number, level, and length
	ucMsgBuf[MSG_IDX_ID]        = MSG_ID_BEACON;
	ucMsgBuf[MSG_IDX_FLG]       = 0x20;
	ucMsgBuf[MSG_IDX_NUM_HI]    = 0x00;
	ucMsgBuf[MSG_IDX_NUM_LO]    = 0x00;
    ucMsgBuf[MSG_IDX_LEN]       = 16;
    ucMsgBuf[MSG_IDX_SRC_LEVEL] = ucGLOB_myLevel;

	//Stuff the source address
	vL2FRAM_copySnumLo16ToBytes(&ucMsgBuf[MSG_IDX_ADDR_HI]);

	//Stuff group ID
	ucMsgBuf[MSG_IDX_GID_HI] = ucGID_getWholeSysGidHiByte();
	ucMsgBuf[MSG_IDX_GID_LO] = ucGID_getWholeSysGidLoByte();

	//Stuff the sub-second time in seconds
	vMISC_copyUlongIntoBytes((uint32_t) lSyncTimeSec, &ucMsgBuf[BCNMSG_IDX_TIME_SEC_XI], NO_NOINT);

	// Fetch the subsecond time and load it
	uiSubSeconds = uiTIME_getSubSecAsUint();
	ucMsgBuf[BCNMSG_IDX_TIME_SUBSEC_HI] = (uint8_t)(uiSubSeconds >> 8);
	ucMsgBuf[BCNMSG_IDX_TIME_SUBSEC_LO] = (uint8_t) uiSubSeconds;

	// Set the packet size
	ucPacketSize = ucMsgBuf[MSG_IDX_LEN] + NET_HDR_SZ + CRC_SZ;

	/* COMPUTE THE CRC */
	ucCRC16_compute_msg_CRC(CRC_FOR_MSG_TO_SEND, ucMsgBuf, ucPacketSize);

} //END: vBuildBeacon()



///////////////////////////////////////////////////////////////////////////////
//! \brief Waits for the request to join message
//!
//! \param none
//! \return 0 for success or 1 for failure
///////////////////////////////////////////////////////////////////////////////
static int8_t cWaitForRequestToJoin(void)
{
    enum
    {
        chkMsgFields  = CHKBIT_CRC + CHKBIT_MSG_TYPE + CHKBIT_DEST_SN,
        rprtMsgFields = CHKBIT_CRC + CHKBIT_MSG_TYPE + CHKBIT_DEST_SN
    };

    int8_t   cRetVal           = -1;  // Assume timeout
	uint8_t  ucIntegrityRetVal;
	uint16_t uiOtherGuysSN;
	uint32_t uslRandNum;
	uint8_t  ucTotalEdges;
	uint8_t  ucMsgIndex;
	S_Edge   S_Edges[10];
	uint8_t  ucFoundTskIndex;
	uint8_t  ucMsgBuf[MAX_RESERVED_MSG_SIZE];
    uint8_t  ucDEBuf[MAX_DE_LEN];

	vTime_SetLinkSlotAlarm(ON);

	//Wait for replies
	while (TRUE)
	{
		// Start the receiver and wait for RTJ
		vADF7020_TXRXSwitch(RADIO_RX_MODE);

		if (ucComm_waitForMsgOrTimeout(ucMsgBuf, MAX_RESERVED_MSG_SIZE, false) == 0)
		{
			// Time is up, exit
			break;
		}
		else
		{
			//Check the message integrity
			ucIntegrityRetVal = ucComm_chkMsgIntegrity(ucMsgBuf, chkMsgFields, rprtMsgFields, MSG_ID_REQUEST_TO_JOIN, 0, uiL2FRAM_getSnumLo16AsUint());

			// If the message is good
			if (ucIntegrityRetVal == 0)
			{
				//Save message data
				uiOtherGuysSN = uiMISC_buildUintFromBytes(&ucMsgBuf[MSG_IDX_ADDR_HI], NO_NOINT);
				uslRandNum    = ulMISC_buildUlongFromBytes(&ucMsgBuf[MSG_IDX_RANDSEED_XI], NO_NOINT);

				/* STASH THE LINKUP SN */
				uiaLinkSN[ucLinkSNidx++] = uiOtherGuysSN;

				ucTotalEdges = ucMsgBuf[MSG_IDX_NUM_EDGES];

#if 1
				/* REPORT TO CONSOLE */
				vSERIAL_sout("Edges: ", 7);
				vSERIAL_UI8out(ucTotalEdges);
				vSERIAL_crlf();
#endif

				ucMsgIndex = MSG_IDX_EDGE_DISC;

				for (uint8_t i = 0; i < ucTotalEdges; ++i)
				{
					S_Edges[i].m_uiSrc   = (uint16_t) (ucMsgBuf[ucMsgIndex++] << 8);
					S_Edges[i].m_uiSrc  |= (uint16_t) ucMsgBuf[ucMsgIndex++];
					S_Edges[i].m_uiDest  = (uint16_t) (ucMsgBuf[ucMsgIndex++] << 8);
					S_Edges[i].m_uiDest |= (uint16_t) ucMsgBuf[ucMsgIndex++];
				}

				ucRoute_NodeJoin(0, uiOtherGuysSN, S_Edges, (int16_t) ucTotalEdges);

				// If a RTJ is received from a node that is already in the task list then it must have
				// dropped the link.  Therefore, we delete the task and initiate a new link with the node.
				// This assumes that there are no duplicate node IDs in the network
				ucFoundTskIndex = ucTask_SearchforLink(uiOtherGuysSN);

				if (ucFoundTskIndex != INVALID_TASKINDEX)
				{
                    // If the node has been found then remove it from the link block, routing table, and remove the task
					ucLNKBLK_RemoveNode(uiOtherGuysSN);
					ucRoute_NodeUnjoin(uiOtherGuysSN);
					ucTask_DestroyTask(ucFoundTskIndex);

                    // Build the report data element stating that the link has been broken
                    vComm_DE_BuildReportHdr(ucDEBuf, CP_ID, 4, ucMAIN_GetVersion());
                    ucMsgIndex = DE_IDX_RPT_PAYLOAD;

                    ucDEBuf[ucMsgIndex++] = SRC_ID_LINK_BROKEN;
                    ucDEBuf[ucMsgIndex++] = 2; // data length
                    ucDEBuf[ucMsgIndex++] = (uchar) (uiOtherGuysSN >> 8);
                    ucDEBuf[ucMsgIndex++] = (uchar) uiOtherGuysSN;

                    // Store DE
                    vReport_LogDE(ucDEBuf, RPT_PRTY_LINK_BROKEN);
				}

				// Create the operational message task here
				ucTask_CreateOMTask(uiOtherGuysSN, uslRandNum, PARENT);

#if 1
				/* REPORT TO CONSOLE */
				vSERIAL_sout("RTJ<", 4);
				vSERIAL_UI16out(uiOtherGuysSN);
				vSERIAL_crlf();
#endif

				// If nodes joined then return the count
				cRetVal = ucLinkSNidx;
			} // End: if(ucIntegrityRetVal)
		} // End: else

		if (ucFLAG3_BYTE.FLAG3_STRUCT.FLG3_LINKSLOT_ALARM == 1) //Link slot ended
			break;
	} //End while(1)

	// Shut off the alarm
	vTime_SetLinkSlotAlarm(OFF);

	return cRetVal;

} //END: cWaitForRequestToJoin()

///////////////////////////////////////////////////////////////////////////////
//! \brief Sends the beacon message
//!
//! @param none
//! @return none
///////////////////////////////////////////////////////////////////////////////
void vComm_SendBeacon(void)
{
    enum
    {
        numBeacons = 2
    };

	long lCurSec;
	signed char cReply;
	uchar ucc;
	uchar i = 0;
	uchar ucPayloadLength;
	uchar ucMsgIndex;
	uchar ucResponseCount = 0;
	uchar ucLinkIdx       = 0;

	//Set the channel
	unADF7020_SetChannel(DISCOVERY_CHANNEL);

	//Power up and initialize the radio
	vADF7020_WakeUp();

	//Get the current time
	lCurSec = lTIME_getSysTimeAsLong();

	while (i < numBeacons)
	{
		//Prepend network layer with an illegal destination address
		vComm_NetPkg_buildHdr(0xFFFF);

		//Build the Beacon message
		vBuildBeacon(lCurSec);

		//Load message into TX buffer.
		vADF7020_SetPacketLength(ucaMSG_BUFF[MSG_IDX_LEN] + NET_HDR_SZ + CRC_SZ);
		unADF7020_LoadTXBuffer((uint8*) &ucaMSG_BUFF);

		// Set state to TX mode
		vADF7020_TXRXSwitch(RADIO_TX_MODE);

		//Send the Message
		vADF7020_SendMsg();

		// Init cReply
		cReply = 0;
			//Wait for replies from nodes
		cReply = cWaitForRequestToJoin();

		// If there wasn't a time out then add the responses
		if (cReply != -1) {
			ucResponseCount += cReply;
		}

		// If there is no room left in the link table then exit
		if(ucLNKBLK_FindEmptyBlk(&ucLinkIndx) != 0)
			break;

		// Increment the breakout condition
		i++;
	}

	//Shutdown the radio
	vADF7020_Quit();

	// If there was a timeout or no nodes replied then exit
  if(ucResponseCount == 0)
  	return;

  // The payload has two bytes for each serial number and one for the source ID
	ucPayloadLength = ucResponseCount * 2 + 2;

	// Build the report data element header
	vComm_DE_BuildReportHdr(CP_ID, ucPayloadLength, ucMAIN_GetVersion());
	ucMsgIndex = DE_IDX_RPT_PAYLOAD;
	ucaMSG_BUFF[ucMsgIndex++] = SRC_ID_CHILD_JOINED;
	ucaMSG_BUFF[ucMsgIndex++] = ucResponseCount * 2;
	// Write the serial numbers of the joined nodes to the report
	for (ucc = 0; ucc < ucResponseCount; ucc++)
	{
		ucaMSG_BUFF[ucMsgIndex++] = (uchar) (uiaLinkSN[ucc] >> 8);
		ucaMSG_BUFF[ucMsgIndex++] = (uchar) uiaLinkSN[ucc];
	}

	//Indicate to listeners that the link is established
	if (ucResponseCount != 0) {
		vBUZ_tune_Blip();
	}

	// Store DE
	vReport_LogDE(ucDEBuf, RPT_PRTY_CHILD_JOINED);

} //END: vComm_SendBeacon()

///////////////////////////////////////////////////////////////////////////////
//! \brief Waits to receive the Beacon message
//!
//!
//! @param none
//! @return ucReturnCode: 1 if failed, 0 for success
///////////////////////////////////////////////////////////////////////////////
static uchar ucComm_WaitFor_Beacon(void)
{
	uchar ucReturnCode; //!< Return code
	uchar ucSrcLevel; //!< Source level in network
	uint uiSrcSN; //!< Serial number of source
	uchar ucFoundStblIdx; //!<Index of source in scheduler table if it exists

	// Assume that we have already timed out
	ucReturnCode = TIMEOUTERR;

	while (ucTimeCheckForAlarms(SUBSLOT_WARNING_ALARM_BIT) == 0) {
		//There is still time, reset return code
		ucReturnCode = 0x00;

		if (ucComm_waitForMsgOrTimeout(YES_RSSI)) {

			/* GOT A MSG -- CHK FOR: CRC, MSGTYPE, GROUPID, DEST_SN */
			if (!(ucComm_chkMsgIntegrity( //RET: Bit Err Mask, 0 if OK
					CHKBIT_CRC + CHKBIT_MSG_TYPE, //chk flags
					0, //CHKBIT_CRC + CHKBIT_MSG_TYPE, //report flags
					MSG_ID_BEACON, //msg type
					0, //src SN
					0 //Dst SN
					))) {

				//check the link level to make sure that the network maintains the child to parent tree structure
				ucSrcLevel = ucaMSG_BUFF[MSG_IDX_SRC_LEVEL];
				if (ucSrcLevel >= ucGLOB_myLevel) {
#if 0
					/* POST A REJECT MSG */
					vSERIAL_sout("Bcn Rjt:Lvl, My=", 16);
					vSERIAL_HB8out(ucGLOB_myLevel);
					vSERIAL_sout(" Bcn=", 5);
					vSERIAL_HB8out(ucSrcLevel);
					vSERIAL_crlf();
#endif
					//set the return variable to indicate an error
					ucReturnCode |= SRCLVLERR; //set the source level error flag
				}

				//Check for a pre-existing link to avoid multiple links between the same nodes
				uiSrcSN = uiMISC_buildUintFromBytes((uchar *) &ucaMSG_BUFF[MSG_IDX_ADDR_HI], NO_NOINT);
				ucFoundStblIdx = ucTask_SearchforLink(uiSrcSN);

				/* IF PRE-EXISTING -- DON'T RECONNECT */
				if (ucFoundStblIdx != 0xFF) {
#if 0
					/* REPORT TO CONSOLE THAT WE ALREADY HAVE THIS LINK */
					vSERIAL_sout("Beacon Rejected:PrevLk=", 23);
					vSERIAL_UI16out(uiSrcSN);
					vSERIAL_crlf();
#endif
					ucReturnCode |= PREXISTLNKERR; //set the pre-existing link error flag
				}

				// If the signal strength is too low then reject
				if(iADF7020_RequestRSSI() < -90)
					ucReturnCode |= RSSIERR;

				// If the message passed all checks then break out
				if(ucReturnCode == 0)
					break;

			}
			else {
				//If we are here then the message failed the integrity check
				ucReturnCode |= MSGINTGRTYERR; //set the message integrity error flag
			}
		} //End: if(ucComm_waitForMsgOrTimeout)
		else {

			//The slot timed out before a message was received
			ucReturnCode |= TIMEOUTERR;
			break;
		}

		// Reset the radio in the event that the message failed the integrity check
		vADF7020_TXRXSwitch(RADIO_RX_MODE);
	}
	return ucReturnCode;
} //END: ucComm_Wait_for_Beacon()


///////////////////////////////////////////////////////////////////////////////
//! \brief Waits to receive the Beacon message and responds with a Request to Join
//! message
//!
//! The discovery slot is divided into sub slots to allow multiple children to
//! respond to a single beacon message.  Without this feature several children
//! would request to join at the same time causing packet collisions.
//!
//! @param none
//! @return none
///////////////////////////////////////////////////////////////////////////////
void vComm_Request_to_Join(void)
{
	ulong uslRandSeed;
	ulong ulRandLinkSlot;
	ulong ulSlotStartTime_sec;
	uint uiMsgXmitOffset_clks;
	uint uiDest;
	uint uiSubSecLatency;
	uint uiSubSecTemp;
	uint uiOtherGuysSN;
	uchar ucMsgIndex;

	/* INC THE RTJ COUNTER */
	uiGLOB_TotalRTJ_attempts++;

	// Make sure the link slot timer is off so it won't set off an alarm
	vTime_SetLinkSlotAlarm(OFF);

	//Configure the timer to measure latency
	vTime_LatencyTimer(ON);

	//set the channel
	unADF7020_SetChannel(DISCOVERY_CHANNEL);

	//Power up and initialize the radio
	vADF7020_WakeUp();

	//if we have received a beacon message
	if (ucComm_WaitFor_Beacon() == 0) {
		//Stop the latency timer
		vTime_LatencyTimer(OFF);

		//read time from the timer register
		uiSubSecLatency = LATENCY_TIMER;

		// Save the new time in Clk2, therefore Clk1 and alarms are still good
		vTIME_setClk2FromBytes((uchar *) &ucaMSG_BUFF[BCNMSG_IDX_TIME_SEC_XI]);

		// Determine the new timer value from the current value + measured value + constant
		uiSubSecTemp = uiMISC_buildUintFromBytes((uchar *) &ucaMSG_BUFF[BCNMSG_IDX_TIME_SUBSEC_HI], 0);

		uiSubSecTemp += (uiSubSecLatency + 0x69);

		// Update the timer register
		vTIME_setSubSecFromUint(uiSubSecTemp);

#if 0
		vSERIAL_sout("Latency Time = ", 15);
		vSERIAL_HB16out(uiSubSecLatency);
		vSERIAL_crlf();

		vSERIAL_sout("Updated Time = ", 15);
		vSERIAL_HB16out(uiSubSecTemp);
		vSERIAL_crlf();
#endif

		// Set the flags to indicate we have network time
		ucFLAG0_BYTE.FLAG0_STRUCT.FLG0_HAVE_WIZ_GROUP_TIME_BIT = 1; //we have group time
		ucFLAG0_BYTE.FLAG0_STRUCT.FLG0_RESET_ALL_TIME_BIT = 1;

		/* SAVE THE LEVEL */
		ucGLOB_myLevel = ucaMSG_BUFF[MSG_IDX_SRC_LEVEL] + 1;

		/* SAVE THE GROUP ID */
		vGID_setWholeSysGidFromBytes((uchar *) &ucaMSG_BUFF[MSG_IDX_GID_HI]);

		//Save parent ID
		uiOtherGuysSN = uiMISC_buildUintFromBytes((uchar *) &ucaMSG_BUFF[MSG_IDX_ADDR_HI], NO_NOINT);

		/*-----------------  COMPUTE THE RTJ REPLY TIME  ------------------------*/

		// choose a random link slot to respond in
		ulRandLinkSlot = (ulong) (ucRAND_getRolledMidSysSeed() % MAX_LINKS_PER_SLOT);

#if 0
		vSERIAL_sout("ulRandLinkSlot= ", 16);
		vSERIAL_HBV32out(ulRandLinkSlot);
		vSERIAL_crlf();
#endif

		/* COMPUTE THE SLOT START TIME */
		ulSlotStartTime_sec = (ulong) lTIME_getClk2AsLong();

//		// TODO remove
//		ulRandLinkSlot = 0;

		// Compute the reply time: time now + randomly selected offset
		uiMsgXmitOffset_clks = uiSubSecTemp + ucaLinkSlotTimes[(uchar) ulRandLinkSlot];

		//Get a random seed to coordinate the next slot for communication
		uslRandSeed = uslRAND_getRolledFullSysSeed(); //get a new rand seed

		//copy the destination address into
		uiDest = ((ucaMSG_BUFF[NET_IDX_SRC_HI] << 8) | ucaMSG_BUFF[NET_IDX_SRC_LO]);

		//Build the network layer header
		vComm_NetPkg_buildHdr(uiDest);

		//Build the request to join message
		vBuildRequestToJoin(uslRandSeed);

		//Send the Message
		ucComm_doSubSecXmit(ulSlotStartTime_sec, uiMsgXmitOffset_clks, USE_CLK2, NO_RECEIVER_START);

		//Shutdown the radio once the RTJ is sent
		vADF7020_Quit();

#if 0
		{
			/* REPORT TO CONSOLE TRANSMIT TIMES */
			vSERIAL_sout("XmtTm=", 6);
			vSERIAL_HB32out(ulSlotStartTime_sec);
			vSERIAL_sout(":", 1);
			vSERIAL_HB16out(uiMsgXmitOffset_clks);
		}
#endif

		//Clear the RTJ slots
		vRTS_convertAllRTJslotsToSleep();

#if 1
		/* REPORT TO CONSOLE */
		vSERIAL_sout("BCN<", 4);
		vSERIAL_UI16out(uiOtherGuysSN);
		vSERIAL_crlf();
#endif

		//Indicate to listeners that the link is established
		vBUZ_tune_Blip();

		// Create the operational message task here
		ucTask_CreateOMTask(uiDest, //dest serial num
				uslRandSeed, //Random seed
				CHILD);

		// Start the frequency synchronization index at 0
		ucFreqAdjustIndex = 0;

		// Build the report data element header
		vComm_DE_BuildReportHdr(CP_ID, 4, ucMAIN_GetVersion());
		ucMsgIndex = DE_IDX_RPT_PAYLOAD;
		ucaMSG_BUFF[ucMsgIndex++] = SRC_ID_JOINED_NET;
		ucaMSG_BUFF[ucMsgIndex++] = 2;
		ucaMSG_BUFF[ucMsgIndex++] = (uchar) (uiDest >> 8);
		ucaMSG_BUFF[ucMsgIndex++] = (uchar) uiDest;

		// Store DE
		vReport_LogDataElement(RPT_PRTY_JOINED_NET);

	} //End: if(!ucComm_Wait_for_Beacon())
	else {
		//Shutdown the radio, no beacon received
		vADF7020_Quit();

		//Stop the latency timer
		vTime_LatencyTimer(OFF);
	}

} //End: vComm_Request_to_Join()



///////////////////////////////////////////////////////////////////////////////
//! \fn vSetDiscMode
//! \brief Sets the discovery mode
//! \param ucMode, the desired mode
///////////////////////////////////////////////////////////////////////////////
void vComm_SetDiscMode(uint8_t ucMode)
{
    S_Discovery.m_ucMode        = ucMode;
    S_Discovery.m_ulStartTime   = lTIME_getSysTimeAsLong();
    S_Discovery.m_ulMaxDuration = ulaDiscDuration[ucMode];
}



///////////////////////////////////////////////////////////////////////////////
//! \fn vGetDiscMode
//! \brief Gets the current discovery settings
//! \param *S_Disc
///////////////////////////////////////////////////////////////////////////////
void vComm_GetDiscMode(T_Discovery *S_Disc)
{
    S_Disc->m_ucMode        = S_Discovery.m_ucMode;
    S_Disc->m_ulStartTime   = S_Discovery.m_ulStartTime;
    S_Disc->m_ulMaxDuration = S_Discovery.m_ulMaxDuration;
}



//! @}

